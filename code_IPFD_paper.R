#code for IPFD paper

#load packages
{
  library(data.table)
  library(readxl)
  library(dplyr)
  library(tidyverse)
  library(plyr)
  library(lubridate) 
  library(survival)
  library(survminer)
  library(ggplot2)
  library(ggpubr)
  library(ggbreak)
  library(gtsummary)
  library(nortest) 
  library(jstable)  
  library(forestploter)  
  library(car)
  library(cols4all)
  library(riskRegression)
  library(adjustedCurves)
  library(tableone)
  library(MatchIt)
  library(mice)
  library(purrr)
  library(Hmisc)
  library(corrplot)
  library(mediation)
  library(rms)
  library(splines)
  library(pROC)
  library(boot)
  library(caret)
  library(mediation)
}

#load data from UK Biobank RAP as Ukb (dataframe)
#prepare table named table_icd10 to match field id and ICD-10 diseases
#set follow up date
date_follow_up=ymd_h('2024-10-31 24')
#prepare ICD-10 data for survival analysis (disease status and time)
{
data_icd10<-data.frame(eid=ukb$eid,
                       date_recruitment=as.POSIXct(ukb$`53-2.0`),
                       death_date0=as.POSIXct(ukb$`40000-0.0`),
                       death_date1=as.POSIXct(ukb$`40000-1.0`),
                       date_lost_follow=ukb$`191-0.0`
)
data_icd10$death_date1[which(is.na(data_icd10$death_date1))]<-data_icd10$death_date0[which(is.na(data_icd10$death_date1))]
nodata<-c()
for (i in 1:nrow(table_icd10)) {
  icd<-table_icd10$`ICD10`[i]
  id<-table_icd10$`F_id`[i]
  if (length(grep(paste0('^',paste0(id,'-')),colnames(ukb)))==0){
    nodata<-c(nodata,i)
    next
  }
  #icd status
  data_icd10$status_icd<-as.POSIXct(ukb[[grep(paste0('^',paste0(id,'-')),colnames(ukb))]])
  data_icd10$status_icd<-ifelse(is.na(data_icd10$status_icd),0,1)
  #icd time 
  data_icd10$time_icd<-as.POSIXct(ukb[[grep(paste0('^',paste0(id,'-')),colnames(ukb))]])
  data_icd10$time_icd[is.na(data_icd10$time_icd)]<-data_icd10$date_lost_follow[is.na(data_icd10$time_icd)]
  data_icd10$time_icd[is.na(data_icd10$time_icd)]<-data_icd10$death_date1[is.na(data_icd10$time_icd)]
  data_icd10$time_icd[is.na(data_icd10$time_icd)]<-date_follow_up
  data_icd10$time_icd<-difftime(data_icd10$time_icd,data_icd10$date_recruitment,units = 'weeks')%>%
    as.numeric()%>%
    round(.,2)
  #icd 命名
  colnames(data_icd10)[grep('status_icd',colnames(data_icd10))]<-paste0('status_',icd)
  colnames(data_icd10)[grep('time_icd',colnames(data_icd10))]<-paste0('time_',icd)
}
#death status
data_icd10$status_death<-data_icd10$death_date1
data_icd10$status_death<-ifelse(is.na(data_icd10$status_death),0,1)
#death time
data_icd10$time_death<-data_icd10$death_date1%>%
  as.POSIXct()
data_icd10$time_death[is.na(data_icd10$time_death)]<-data_icd10$date_lost_follow[is.na(data_icd10$time_death)]
data_icd10$time_death[is.na(data_icd10$time_death)]<-date_follow_up
data_icd10$time_death<-difftime(data_icd10$time_death,data_icd10$date_recruitment,units = 'weeks')%>%
  as.numeric()%>%
  round(.,2)
#save data_icd10
saveRDS(data_icd10,'data/data_icd10.RData')
}

#prepare baseline data
{
field_id_baseline<-c('^21022-',"^31-","^21000-", "^20116-","^20117-","^21001-","^22189-",'^21088-','^22040-',"^48-",'^21090-')
field_name_baseline<-c('age','sex','ethnicity','smoking','alcohol','bmi','TDI','liver_fat','MET_minutes','waist','IPFD')
#set baseline time
n_base <- '-2.0'  
data=ukb[,'eid',drop=F]
for (i in seq_along(field_id_baseline)) {
  cols=grep(field_id_baseline[i],colnames(ukb))%>%as.vector()
  n=length(cols)
  df=ukb[,..cols,drop=F]
  if (n==1){
    data[[field_name_baseline[i]]]=df[[1]]
  } else if (grep(n_base,colnames(df))==1){
    data[[field_name_baseline[i]]]=df[[1]]
  }
  else {
    df=df[,1:grep(n_base,colnames(df)),drop=F]
    last_col_pos <- ncol(df)          
    prev_cols <- rev(names(df)[-last_col_pos])  
    data[[field_name_baseline[i]]] <- reduce(
      .init = df[[last_col_pos]],        
      .x = prev_cols,                   
      .f = ~ coalesce(.x, df[[.y]]),     
      .dir = "forward"                   
    )
  }
}
#calculate age at baseline
data$age=difftime(as.POSIXct(ukb$`53-2.0`),as.POSIXct(ukb$`53-0.0`),units = 'days')%>%
  as.numeric()/365.2425+data$age
data$age=round(data$age)

data$sex<-factor(data$sex,levels = c(0,1),labels = c('Female','Male'))
data$smoking[data$smoking==-3]<-NA
data$smoking[data$smoking==2]=1
data$smoking<-factor(data$smoking,levels = c(0,1),
                     labels = c('Never','Previous or current'))
data$alcohol[data$alcohol==-3]<-NA
data$alcohol[data$alcohol==2]=1
data$alcohol<-factor(data$alcohol,levels = c(0,1),
                     labels = c('Never','Previous or current'))
data$ethnicity[data$ethnicity %in% c(1,1001,2001,3001,4001)]<-1
data$ethnicity[data$ethnicity %in% c(2,1002,2002,3002,4002)]<-2
data$ethnicity[data$ethnicity %in% c(3,1003,2003,3003,4003)]<-3
data$ethnicity[data$ethnicity %in% c(4,2004,3004)]<-4
data$ethnicity[data$ethnicity==5]<-5
data$ethnicity[data$ethnicity==6]<-6
data$ethnicity[data$ethnicity==-1]<-NA
data$ethnicity[data$ethnicity==-3]<-NA
data$ethnicity<-ifelse(data$ethnicity==1,1,0)
data$ethnicity<-factor(data$ethnicity,levels = c(0,1),labels = c('Non-white','White'))

data=na.omit(data)

#set independent variable
quantile(data$IPFD,probs = c(0.25,0.5,0.75))
data$IPFD_cut=cut(data$IPFD,breaks=c(0,4.83,8.02,13.64,Inf))
covariants=c('age', 'sex', 'ethnicity', 'smoking', 'alcohol', 'bmi', 'TDI', 'liver_fat', 'MET_minutes', 'waist')
#scale
data$age_ori=data$age
data$bmi_ori=data$bmi
data$TDI_ori=data$TDI
data$liver_fat_ori=data$liver_fat
data$MET_minutes_ori=data$MET_minutes
data$waist_ori=data$waist
data$IPFD_ori=data$IPFD
scale_vars <- c("age", "bmi",'TDI','liver_fat', 'MET_minutes', 'waist','IPFD')  # 手动填写需要标准化的列名
data=data %>%
  mutate(across(all_of(scale_vars), 
                ~ scale(., center = TRUE, scale = TRUE) %>% 
                  as.vector))  
data$fatty_liver=ifelse(data$liver_fat_ori>=6.5,'Yes','No')
data$fatty_liver=factor(data$fatty_liver,levels = c('No','Yes'))
data$bmi_obe=ifelse(data$bmi_ori<30,0,1)
#save baseline data
saveRDS(data,'data/data250510.RData')
#saveRDS(data,'data/data_mice.RData')
}

#Survival analysis
{
n_positive=90
statuses<-grep('^status_',colnames(data_ICD10),value = T)
statuses<-statuses[-grep('^status_death',statuses)]
times<-grep('^time_',colnames(data_ICD10),value = T)
times<-times[-grep('^time_death',times)]#1131
ICD10<-sub('status_','',statuses)
diseases<-table_icd10$Disease[match(ICD10,table_icd10$ICD10)]

status_counts<- sapply(data_ICD10[, statuses], function(col) sum(col == 1, na.rm = TRUE))
columns_zero <- names(status_counts[status_counts == 0])
columns_less_n_positive <- names(status_counts[status_counts > 0 & status_counts < n_positive])                       
statuses<-setdiff(statuses,c(columns_zero,columns_less_n_positive))
times<-gsub('status','time',statuses)
ICD10<-sub('status_','',statuses)
diseases<-table_icd10$Disease[match(ICD10,table_icd10$ICD10)]

valid_columns<- sapply(times, function(time_col) {
  status_col <- sub("^time", "status", time_col)
  rows_gt_48 <- data_ICD10[[time_col]] > 0
  status_eq_1_count <- sum(data_ICD10[[status_col]][rows_gt_48] == 1, na.rm = TRUE)
  if (status_eq_1_count >= n_positive) {
    return(time_col)
  } else {
    return(NA)
  }
}, USE.NAMES = FALSE)
valid_columns <- na.omit(valid_columns)
columns_time48_less_150<-setdiff(times,valid_columns)
times<-valid_columns
statuses<-gsub('time','status',times)
ICD10<-sub('status_','',statuses)
diseases<-table_icd10$Disease[match(ICD10,table_icd10$ICD10)]

cres<-NULL
cox_model3<-NULL
cox_model3_fit<-list()
VIFs<-list()
zphs<-list()
variable='IPFD'
formula<- as.formula(paste0("Surv(time, status)~", variable,"+",
                            paste0(covariants, collapse = " + ")))
for(i in 1:length(statuses)){
  data_cox=data
  data_cox$status=data_ICD10[[statuses[i]]]
  data_cox$time=data_ICD10[[times[i]]]
  data_cox<-data_cox[which(data_cox$time>0),]
  cox<-coxph(formula,data = data_cox,na.action=na.omit)
  zph<-cox.zph(cox)
  zphs[[i]]<-zph[[1]]
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],3)
  CI95 <-round(cox1$conf.int[1,4],3)
  VIF<-vif(cox)
  VIFs[[i]]<-VIF
  zph<-zphs[[i]][,3][nrow(zphs[[i]])]
  res<- data.frame('ICD 10' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'VIF'=mean(VIF>10),
                   'zph'=zph,
                   'N'=nrow(data_cox),
                   'N_yes'=length(which(data_cox$status==1)),
                   'Disease' = diseases[i]
                   
  )
  cox_model3<-rbind(cox_model3,res)
}
cox_model3=cox_model3[-which(cox_model3$Disease=='Obesity'),]
cox_model3$p_adj<-p.adjust(cox_model3$p,'BH')
write.csv(cox_model3, file = "table/cox_model.csv")

#extended cox models
res<-NULL
cox_model3t<-NULL
cox_model3t_fit<-list()
VIFs<-list()
non_tt_names<-c()
grep(paste0(cox_model3$ICD.10[which(cox_model3$zph<0.05)],collapse = '|'),statuses)
for(i in grep(paste0(cox_model3$ICD.10[which(cox_model3$zph<0.05)],collapse = '|'),statuses)){
  data_cox=data
  data_cox$status=data_ICD10[[statuses[i]]]
  data_cox$time=data_ICD10[[times[i]]]
  data_cox<-data_cox[which(data_cox$time>0),]
  tt_names<-names(which(zphs[[i]][,3][-nrow(zphs[[i]])]<0.05))%>%
    setdiff(.,non_tt_names)
  formula=as.formula(paste0('Surv(time,status)~',variable,'+',paste0(covariants,collapse = '+'),'+',
                            paste0('tt(as.numeric(',tt_names)%>%
                              paste0(.,'))')%>%
                              paste(.,collapse = "+"))
  )
  
  
  cox<-coxph(formula,data = data_cox,tt=function(x,t,...)x*log(t+1)) 
  cox_model3t_fit[[i]]<-cox
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],3)
  CI95 <-round(cox1$conf.int[1,4],3)
  res<- data.frame('ICD 10' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'zph'=zphs[[i]][,3][nrow(zphs[[i]])],
                   'N'=nrow(data_cox),
                   'N_yes'=length(which(data_cox$status==1)),
                   'Disease' = diseases[i],
                   'tv-covariants'=paste(names(which(zphs[[i]][,3][-nrow(zphs[[i]])]<0.05)),collapse = '|')
  )
  cox_model3t<-rbind(cox_model3t,res)
}
write.csv(cox_model3t, file = "table/cox_model_td.csv")

#Sorting table format
cox=fread("table/cox_model.csv")
cox.t=fread("table/cox_model_td.csv")
cox=cox[-grep(paste0(cox.t$ICD.10[grep('IPFD',cox.t$tv.covariants)],collapse = '|'),cox$ICD.10),]
cox.t=cox.t[-grep('IPFD',cox.t$tv.covariants),]
for (i in seq_along(cox.t$ICD.10)) {
  cox[grep(cox.t$ICD.10[i],cox$ICD.10),3:7]=cox.t[i,3:7]
}
cox$p_adj=p.adjust(cox$p,method = 'BH')
cox$`Cumulative incidence,%(N cases/N total)`<-round(cox$N_yes/cox$N*100,2)%>%
  paste0(.,' (',cox$N_yes,'/',cox$N,')')
cox$`95% CI`<-paste0('(',sprintf("%.3f", cox$CI5),', ',sprintf("%.3f",cox$CI95),')')
cox$`Extended cox model`<-ifelse(cox$zph<0.05,'Yes','No')
cox$`PH assumption`<-ifelse(cox$zph<0.05,'Unsatisfied','Satisfied')
cox$VIF=ifelse(cox$VIF==0,'No','Yes')
cox.export=cox%>%transmute(
  Disease=Disease,
  `ICD-10`=ICD.10,
  `Cumulative incidence,%(N cases/N total)`=`Cumulative incidence,%(N cases/N total)`,
  `Hazard ratio`=HR,
  `95% CI of hazard ratio`=`95% CI`,
  `P-value`=p,
  `False discovery rate`=p_adj,
  `PH assumption`=`PH assumption`,
  `Extended cox model`=`Extended cox model`
)
cox.export$`P-value`=sprintf("%.3f",cox.export$`P-value`)%>%as.character()
cox.export$`False discovery rate`=sprintf("%.3f",cox.export$`False discovery rate`)%>%as.character()
cox.export$`Hazard ratio`=sprintf("%.3f",cox.export$`Hazard ratio`)%>%as.character()
cox.export=cox.export[order(cox.export$`False discovery rate`), ]
fwrite(cox.export,file = 'table/obs-PheWAS.csv')
}

#Sensitivity analysis of Survival analysis
{
  #load survival analysis results
  obs=fread("table/obs-PheWAS.csv")
  ICD10=grep(paste0(obs[obs$`False discovery rate`<0.05,]$`ICD-10`,collapse = '|'),obs$`ICD-10`,value = T)
  statuses=paste0('status_',ICD10)
  times=gsub('status','time',statuses)
  diseases<-table_icd10$Disease[match(ICD10,table_icd10$ICD10)]
  
  valid_columns<- sapply(times, function(time_col) {
    status_col <- sub("^time", "status", time_col)
    rows_gt_48 <- data_ICD10[[time_col]] > 0
    status_eq_1_count <- sum(data_ICD10[[status_col]][rows_gt_48] == 1, na.rm = TRUE)
    if (status_eq_1_count >= n_positive) {
      return(time_col)
    } else {
      return(NA)
    }
  }, USE.NAMES = FALSE)
  valid_columns <- na.omit(valid_columns)
  columns_time48_less_150<-setdiff(times,valid_columns)
  times<-valid_columns
  statuses<-gsub('time','status',times)
  ICD10<-sub('status_','',statuses)
  diseases<-table_icd10$Disease[match(ICD10,table_icd10$ICD10)]
  
  cres<-NULL
  cox_model3<-NULL
  cox_model3_fit<-list()
  VIFs<-list()
  zphs<-list()
  variable='IPFD'
  formula<- as.formula(paste0("Surv(time, status)~", variable,"+",
                              paste0(covariants, collapse = " + ")))
  for(i in 1:length(statuses)){
    data_cox=data
    data_cox$status=data_ICD10[[statuses[i]]]
    data_cox$time=data_ICD10[[times[i]]]
    data_cox<-data_cox[which(data_cox$time>12),]
    cox<-coxph(formula,data = data_cox,na.action=na.omit)
    zph<-cox.zph(cox)
    zphs[[i]]<-zph[[1]]
    cox1<-summary(cox)
    beta <- round(cox1$coefficients[1,1],3)
    HR<-round(exp(beta),3)
    PValue <- round(cox1$coefficients[1,5],3)
    CI5 <-round(cox1$conf.int[1,3],3)
    CI95 <-round(cox1$conf.int[1,4],3)
    VIF<-vif(cox)
    VIFs[[i]]<-VIF
    zph<-zphs[[i]][,3][nrow(zphs[[i]])]
    res<- data.frame('ICD 10' = ICD10[i],
                     'beta' = beta,
                     'HR'=HR,
                     'CI5' = CI5,
                     'CI95' = CI95,
                     'p' = PValue,
                     'VIF'=mean(VIF>10),
                     'zph'=zph,
                     'N'=nrow(data_cox),
                     'N_yes'=length(which(data_cox$status==1)),
                     'Disease' = diseases[i]
                     
    )
    cox_model3<-rbind(cox_model3,res)
  }
  cox_model3=cox_model3[-which(cox_model3$Disease=='Obesity'),]
  cox_model3$p_adj<-p.adjust(cox_model3$p,'BH')
  write.csv(cox_model3, file = "table/cox_model.csv")
  
  
  #extended cox models
  res<-NULL
  cox_model3t<-NULL
  cox_model3t_fit<-list()
  VIFs<-list()
  non_tt_names<-c()
  grep(paste0(cox_model3$ICD.10[which(cox_model3$zph<0.05)],collapse = '|'),statuses)
  for(i in grep(paste0(cox_model3$ICD.10[which(cox_model3$zph<0.05)],collapse = '|'),statuses)){
    data_cox=data
    data_cox$status=data_ICD10[[statuses[i]]]
    data_cox$time=data_ICD10[[times[i]]]
    data_cox<-data_cox[which(data_cox$time>12),]
    tt_names<-names(which(zphs[[i]][,3][-nrow(zphs[[i]])]<0.05))%>%
      setdiff(.,non_tt_names)
    formula=as.formula(paste0('Surv(time,status)~',variable,'+',paste0(covariants,collapse = '+'),'+',
                              paste0('tt(as.numeric(',tt_names)%>%
                                paste0(.,'))')%>%
                                paste(.,collapse = "+"))
    )
    
    
    cox<-coxph(formula,data = data_cox,tt=function(x,t,...)x*log(t+1)) 
    cox_model3t_fit[[i]]<-cox
    cox1<-summary(cox)
    beta <- round(cox1$coefficients[1,1],3)
    HR<-round(exp(beta),3)
    PValue <- round(cox1$coefficients[1,5],3)
    CI5 <-round(cox1$conf.int[1,3],3)
    CI95 <-round(cox1$conf.int[1,4],3)
    res<- data.frame('ICD 10' = ICD10[i],
                     'beta' = beta,
                     'HR'=HR,
                     'CI5' = CI5,
                     'CI95' = CI95,
                     'p' = PValue,
                     'zph'=zphs[[i]][,3][nrow(zphs[[i]])],
                     'N'=nrow(data_cox),
                     'N_yes'=length(which(data_cox$status==1)),
                     'Disease' = diseases[i],
                     'tv-covariants'=paste(names(which(zphs[[i]][,3][-nrow(zphs[[i]])]<0.05)),collapse = '|')
    )
    cox_model3t<-rbind(cox_model3t,res)
  }
  write.csv(cox_model3t, file = "table/cox_model_td.csv")
}

#Causal mediation
{
results_df <- data.frame(
  Disease = character(16),
  ICD10= character(16),
  ACME_Est = numeric(16),
  ACME_CI_lower = numeric(16),
  ACME_CI_upper = numeric(16),
  ACME_p = numeric(16),
  ADE_Est = numeric(16),
  ADE_CI_lower = numeric(16),
  ADE_CI_upper = numeric(16),
  ADE_p = numeric(16),
  Prop_Mediated = numeric(16),
  Prop_Mediated_CI_lower = numeric(16),
  Prop_Mediated_CI_upper = numeric(16),
  Prop_Mediated_p = numeric(16),
  Total_Effect = numeric(16),
  Total_Effect_CI_lower = numeric(16),
  Total_Effect_CI_upper = numeric(16),
  Total_Effect_p = numeric(16),
  stringsAsFactors = FALSE
)

covariates_formula <- ~ age + sex + ethnicity + bmi_obe + smoking + 
  alcohol + MET_minutes + fatty_liver

for (i in 1:16) {
  disease_name <- statuses[i + 1]  # statuses[2:17]
  data_m <- data
  data_m$status_E11 <- data_ICD10$status_E11
  data_m$time_E11 <- data_ICD10$time_E11
  data_m$status <- data_ICD10[[disease_name]]
  data_m$time <- data_ICD10[[times[i + 1]]]  # 假设times对应时间变量
  
  data_m <- data_m[data_m$time > 0 & data_m$time_E11 > 0, ]
  
  data_m$status_m <- ifelse(
    data_m$status_E11 == 1 & data_m$time_E11 < data_m$time, 1, 0
  )
  
  med.fit <- glm(
    update.formula(covariates_formula, status_m ~ IPFD + .),
    data = data_m,
    family = binomial(link = "logit")
  )
  
  out.fit <- glm(
    update.formula(covariates_formula, status ~ status_m + IPFD + .),
    data = data_m,
    family = binomial(link = "logit")
  )
  
  med.out <- mediate(
    med.fit, 
    out.fit, 
    treat = "IPFD", 
    mediator = "status_m",
    sims = 1000
  )
  
  results_df[i, "Disease"] <- diseases[i+1]
  results_df[i, "ICD10"] <- ICD10[i+1]
  results_df[i, "ACME_Est"] <- med.out$d.avg
  results_df[i, "ACME_CI_lower"] <- med.out$d.avg.ci[1]
  results_df[i, "ACME_CI_upper"] <- med.out$d.avg.ci[2]
  results_df[i, "ACME_p"] <- med.out$d.avg.p
  results_df[i, "ADE_Est"] <- med.out$z.avg
  results_df[i, "ADE_CI_lower"] <- med.out$z.avg.ci[1]
  results_df[i, "ADE_CI_upper"] <- med.out$z.avg.ci[2]
  results_df[i, "ADE_p"] <- med.out$z.avg.p
  results_df[i, "Prop_Mediated"] <- med.out$n.avg
  results_df[i, "Prop_Mediated_CI_lower"] <- med.out$n.avg.ci[1]
  results_df[i, "Prop_Mediated_CI_upper"] <- med.out$n.avg.ci[2]
  results_df[i, "Prop_Mediated_p"] <- med.out$n.avg.p
  results_df[i, "Total_Effect"] <- med.out$tau.coef
  results_df[i, "Total_Effect_CI_lower"] <- med.out$tau.ci[1]
  results_df[i, "Total_Effect_CI_upper"] <- med.out$tau.ci[2]
  results_df[i, "Total_Effect_p"] <- med.out$tau.p
}
fwrite(results_df, "table/mediation_results.csv")
}

#Subgroup analysis
{
data$`Age group`=ifelse(data$age_ori<60,'<60','≥60')
data$`Age group`=factor(data$`Age group`,levels = c('<60','≥60'))

res<-NULL
cox_model3_group<-NULL
formula0<-'Surv(time,status)~IPFD+sex+age+ethnicity+bmi_obe+smoking+alcohol+MET_minutes+fatty_liver'
res_blank<- data.frame('Characteristics' =NA,
                       'beta' = NA,
                       'HR'=NA,
                       'CI5' = NA,
                       'CI95' = NA,
                       'p' = NA,
                       'wald.test'=NA,
                       'logtest'=NA,
                       'AIC'=NA,
                       'N'=NA,
                       'N_yes'=NA,
                       'Disease' = NA,
                       'group'=NA,
                       'N_group'=NA,
                       'N_group_yes'=NA,
                       'p for interaction'=NA
)
for(i in 1:length(statuses)){
  data1=data
  data1$status=data_ICD10[[statuses[i]]]
  data1$time=data_ICD10[[times[i]]]
  data1<-data1[which(data1$time>0),]
  attach(data1)
  formula<-as.formula(Surv(time,status)~IPFD+
                        sex+age+ethnicity+bmi_obe+smoking+alcohol+MET_minutes+fatty_liver
  )
  #sex
  cox<- coxph(formula,data=data1[which(data1$sex=='Male'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  #P for interaction
  fit1<-coxph(formula,data=data1)
  formula2<-as.formula(paste0(formula0,'+sex*IPFD'))
  fit2<-coxph(formula2,data1)
  p_for_interaction<-anova(fit1,fit2,test='Chisq')[2,4]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='sex_Male',
                   'N_group'=length(which(data1$sex=='Male')),
                   'N_group_yes'=length(which(data1$sex=='Male' & data1$status==1)),
                   'p for interaction'=p_for_interaction
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  cox<- coxph(formula,data=data1[which(data1$sex=='Female'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='sex_Female',
                   'N_group'=length(which(data1$sex=='Female')),
                   'N_group_yes'=length(which(data1$sex=='Female' & data1$status==1)),
                   'p for interaction'=''
                   
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  cox_model3_group<-rbind(cox_model3_group,res_blank)
  
  #age
  cox<- coxph(formula,data=data1[which(data1$`Age group`=='<60'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]

    fit1<-coxph(formula,data=data1)
  formula2<-as.formula(paste0(formula0,'+`Age group`*IPFD'))
  fit2<-coxph(formula2,data1)
  p_for_interaction<-anova(fit1,fit2,test='Chisq')[2,4]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='age_<60',
                   'N_group'=length(which(data1$`Age group`=='<60')),
                   'N_group_yes'=length(which(data1$`Age group`=='<60' & data1$status==1)),
                   'p for interaction'=p_for_interaction
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  cox<- coxph(formula,data=data1[which(data1$`Age group`=='≥60'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='age_≥60',
                   'N_group'=length(which(data1$`Age group`=='≥60')),
                   'N_group_yes'=length(which(data1$`Age group`=='≥60' & data1$status==1)),
                   'p for interaction'=''
                   
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  cox_model3_group<-rbind(cox_model3_group,res_blank)
  
  #white ethnicity
  cox<- coxph(formula,data=data1[which(data1$ethnicity=='Non-white'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]

  fit1<-coxph(formula,data=data1)
  formula2<-as.formula(paste0(formula0,'+ethnicity*IPFD'))
  fit2<-coxph(formula2,data1)
  p_for_interaction<-anova(fit1,fit2,test='Chisq')[2,4]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='ethnicity_non-white',
                   'N_group'=length(which(data1$ethnicity=='Non-white')),
                   'N_group_yes'=length(which(data1$ethnicity=='Non-white' & data1$status==1)),
                   'p for interaction'=p_for_interaction
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  cox<- coxph(formula,data=data1[which(data1$ethnicity=='White'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='ethinicity_white',
                   'N_group'=length(which(data1$ethnicity=='White')),
                   'N_group_yes'=length(which(data1$ethnicity=='Whhite' & data1$status==1)),
                   'p for interaction'=''
                   
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  cox_model3_group<-rbind(cox_model3_group,res_blank)
  
  #smoking
  cox<- coxph(formula,data=data1[which(data1$smoking =='Never'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]

  fit1<-coxph(formula,data=data1)
  formula2<-as.formula(paste0(formula0,'+smoking*IPFD'))
  fit2<-coxph(formula2,data1)
  p_for_interaction<-anova(fit1,fit2,test='Chisq')[2,4]
  
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='smoking_Never',
                   'N_group'=length(which(data1$smoking=='Never')),
                   'N_group_yes'=length(which(data1$smoking=='Never' & data1$status==1)),
                   'p for interaction'=p_for_interaction
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  cox<- coxph(formula,data=data1[which(data1$smoking =='Previous or current'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='smoking_Previous_current',
                   'N_group'=length(which(data1$smoking=='Previous or current')),
                   'N_group_yes'=length(which(data1$smoking=='Previous or current' & data1$status==1)),
                   'p for interaction'=''
                   
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  
  #alcohol
  cox<- coxph(formula,data=data1[which(data1$alcohol =='Never'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]

  fit1<-coxph(formula,data=data1)
  formula2<-as.formula(paste0(formula0,'+alcohol*IPFD'))
  fit2<-coxph(formula2,data1)
  p_for_interaction<-anova(fit1,fit2,test='Chisq')[2,4]
  
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='alchhol_status_Never',
                   'N_group'=length(which(data1$alcohol=='Never')),
                   'N_group_yes'=length(which(data1$alcohol=='Never' & data1$status==1)),
                   'p for interaction'=p_for_interaction
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  cox<- coxph(formula,data=data1[which(data1$alcohol =='Previous or current'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='alchhol_status_Previous',
                   'N_group'=length(which(data1$alcohol=='Previous or current')),
                   'N_group_yes'=length(which(data1$alcohol=='Previous or current' & data1$status==1)),
                   'p for interaction'=''
                   
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  #obesity
  cox<- coxph(formula,data=data1[which(data1$bmi_obe=='No'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  
  fit1<-coxph(formula,data=data1)
  formula2<-as.formula(paste0(formula0,'+bmi_obe*IPFD'))
  fit2<-coxph(formula2,data1)
  p_for_interaction<-anova(fit1,fit2,test='Chisq')[2,4]
  
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='BMI_＜30',
                   'N_group'=length(which(data1$bmi_obe=='No')),
                   'N_group_yes'=length(which(data1$bmi_obe=='No' & data1$status==1)),
                   'p for interaction'=p_for_interaction
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  
  cox<- coxph(formula,data=data1[which(data1$bmi_obe=='Yes'),])
  cox1<-summary(cox)
  beta <- round(cox1$coefficients[1,1],3)
  HR<-round(exp(beta),3)
  PValue <- round(cox1$coefficients[1,5],3)
  CI5 <-round(cox1$conf.int[1,3],2)
  CI95 <-round(cox1$conf.int[1,4],2)
  wald.test<-cox1$waldtest[3]
  logtest<-cox1$logtest[3]
  res<- data.frame('Characteristics' = ICD10[i],
                   'beta' = beta,
                   'HR'=HR,
                   'CI5' = CI5,
                   'CI95' = CI95,
                   'p' = PValue,
                   'wald.test'=wald.test,
                   'logtest'=logtest,
                   'AIC'=AIC(cox),
                   'N'=nrow(data1),
                   'N_yes'=length(which(data1$status==1)),
                   'Disease' = diseases[i],
                   'group'='BMI_≥30',
                   'N_group'=length(which(data1$bmi_obe=='Yes')),
                   'N_group_yes'=length(which(data1$bmi_obe=='Yes' & data1$status==1)),
                   'p for interaction'=''
                   
  )
  cox_model3_group<-rbind(cox_model3_group,res)
  cox_model3_group<-rbind(cox_model3_group,res_blank)
  
  detach(name = data1)
}
cox_model3_group$SE<-(cox_model3_group$CI95 - cox_model3_group$CI5) / (2 * 1.96)
cox_model3_group$`HR (95%)`<-paste0(round(cox_model3_group$HR,2),' (',cox_model3_group$CI5,'-',cox_model3_group$CI95,')')
cox_model3_group$`blank`<-NA
fwrite(cox_model3_group[,c("Disease","group",'N_group_yes','N_group','blank',"HR (95%)",'p.for.interaction',"HR","CI5","CI95",'SE')],file = 'table/cox_model3_subgroup.csv')
}

#Restricted cubic splines
{
calc_slope <- function(OR) {
  slope_df <- data.frame(
    x = OR$x,
    slope = NA_real_
  )
  
  n <- nrow(OR)
  for(i in 1:n) {
    if(i == 1) {
      slope_df$slope[i] <- (OR$yhat[i+1] - OR$yhat[i]) / (OR$x[i+1] - OR$x[i])
    } else if(i == n) {
      slope_df$slope[i] <- (OR$yhat[i] - OR$yhat[i-1]) / (OR$x[i] - OR$x[i-1])
    } else {
      slope_df$slope[i] <- (OR$yhat[i+1] - OR$yhat[i-1]) / (OR$x[i+1] - OR$x[i-1])
    }
  }
  return(slope_df)
}

results_list <- list()
rcs_plot_list <- list()
slope_plot_list <- list()

for (i in 1:17) {
  current_status <- statuses[i]
  current_time <- times[i]
  current_disease <- diseases[i]
  
  data_rcs <- data
  data_rcs$status <- data_ICD10[[current_status]]
  data_rcs$time <- data_ICD10[[current_time]]
  data_rcs <- data_rcs[data_rcs$time > 0, ]
  
  dd <- datadist(data_rcs)
  options(datadist = "dd")
  
  nk <- 3:5
  fits <- lapply(nk, function(nk) {
    fit_rms<- lrm(status~rcs(IPFD_ori,nk)+
                    age+sex+ethnicity+bmi_obe+smoking+alcohol+MET_minutes+fatty_liver
                  , data = data_rcs)
  })
  aics<- sapply(fits, AIC)  
  best_nk <- nk[which.min(aics)]
  
  fit_rms <- lrm(status ~ rcs(IPFD_ori, best_nk) + 
                   age + sex + ethnicity + bmi_obe + smoking + alcohol + MET_minutes + fatty_liver,
                 data = data_rcs)
  
  an <- anova(fit_rms) %>% 
    as.data.frame() %>% 
    rownames_to_column()
  
  p_linear <- an$P[an$rowname == " Nonlinear"]
  p_overall <- an$P[an$rowname == "IPFD_ori"]
  
  format_p <- function(p) {
    case_when(
      p < 0.0001 ~ "<0.0001",
      p < 0.001 ~ "<0.001",
      p < 0.01 ~ "<0.01",
      p < 0.05 ~ "<0.05",
      TRUE ~ as.character(round(p, 3))
    )
  }
  
  OR <- rms::Predict(fit_rms, name = 'IPFD_ori', fun = exp, ref.zero = TRUE, np = 1000)
  colnames(OR)[colnames(OR) == "IPFD_ori"] <- "x"
  xintercept <- OR$x[which.min(abs(1 - OR$yhat))]
  
  results_list[[i]] <- tibble(
    Disease = diseases[i],
    ICD10=ICD10[i],
    Best_knots = best_nk,
    P_overall = round(p_overall,3),
    P_nonlinear = round(p_linear,3),
    Inflection_point = round(xintercept, 2)
  )
  
  slope_df <- calc_slope(OR)
  
  max_points <- slope_df$x[which.max(slope_df$slope)]
  min_points <- slope_df$x[which.min(slope_df$slope)]
  zero1 <- slope_df$x[which(diff(sign(slope_df$slope)) < 0)]
  zero2 <- slope_df$x[which(diff(sign(slope_df$slope)) > 0)]
  
  #x 100%
  xmax=55
  ymax=max(OR$upper[which(OR$x<xmax)])
  ymin=min(OR$lower[which(OR$x<xmax)])
  
  data_rcs$x_ori=data_rcs[['IPFD_ori']]
  x_ori_cut=data_rcs$x_ori[which(data_rcs$x_ori<=xmax)]
  bin_width <- 3          
  breaks <- seq(floor(min(x_ori_cut)), ceiling(max(x_ori_cut)), by = bin_width)
  bin_index <- findInterval(x_ori_cut, breaks, rightmost.closed = TRUE)  # 获取分箱索引
  freq_vector <- tabulate(bin_index, nbins = length(breaks)-1)/length(data_rcs$x_ori)*100
  scale_factor <- ymax / max(freq_vector)
  
  rcs_plot= ggplot() +
    geom_histogram(  
      data = data_rcs, 
      aes(x = x_ori, y = after_stat(count/length(data_rcs$x_ori)*100 * scale_factor)),
      binwidth = bin_width, fill = 'red', alpha = 0.1,color='grey') +
    geom_line(data=OR, aes(x, yhat), 
              linetype="solid", size=1, alpha=0.7, colour="darkred") +
    geom_ribbon(data=OR, aes(x, ymin=lower, ymax=upper),
                alpha=0.1, fill="darkred") +
    scale_y_continuous(
      name = "Odds ratio (95% CI)",
      limits = c(0,ymax),
      expand = c(0,0),
      sec.axis = sec_axis(~./scale_factor, name="Density (%)") 
    ) +
    
    theme_classic()+
    geom_hline(yintercept=1, linetype=2,size=0.75,alpha=0.4)+
    geom_vline(xintercept = xintercept,linetype=2,size=0.75,alpha=0.4)+
    labs(title = diseases[i], x="Intra-pancreatic fat deposition (%)")+
    annotate('text',x=0.6*xmax,y=0.9*ymax,label = paste("Overall P:", format_p(p_overall)))+
    annotate('text',x=0.6*xmax,y=0.8*ymax,label=paste("Nonlinear P:", format_p(p_linear)))+
    scale_x_continuous(limits =c(0,xmax),expand =c(0,0))
  
  rcs_plot_list[[i]] <- rcs_plot
  
  ggsave(paste0("figure/rcs/RCS_plot_", current_status, ".png"), rcs_plot, 
         width = 8, height = 6, dpi = 300)
  
  slope_plot <- ggplot(slope_df, aes(x = x, y = slope)) +
    geom_line(color = "#377eb8", linewidth = 1) +
    geom_hline(yintercept = 0, linetype = "dashed", ,color = "#636363") +
    geom_vline(xintercept = max_points, linetype = 2, ,alpha=0.4) +
    geom_vline(xintercept = min_points, linetype = 2, ,alpha=0.4) +
    annotate("text", x = max_points, y = max(slope_df$slope)*0.8, 
             label = paste0("x=", round(max_points, 2)), 
             color = "black", size = 3, vjust = 0) +
    annotate("text", x = min_points, y = min(slope_df$slope)*0.8, 
             label = paste0("x=", round(min_points, 2)), 
             color = "black", size = 3, vjust = 0) +
    annotate("text", x = zero1, y =0, 
             label = paste0("x=", round(zero1, 2)), 
             color = "black", size = 3, vjust = 0) +
    annotate("text", x = zero2, y =0, 
             label = paste0("x=", round(zero2, 2)), 
             color = "black", size = 3, vjust = 0,hjust=0) +
    labs(title = current_disease,
         x = "Intra-pancreatic fat deposition (%)",
         y = "Slope (d(OR)/d(IPFD))") +
    coord_cartesian(xlim = c(0, xmax)) +
    theme_classic() +
    theme(
      plot.title = element_text(size = 11, face = "bold"),
      axis.title = element_text(size = 9),
      axis.text = element_text(size = 8),
      panel.grid.major = element_line(color = "grey90", linewidth = 0.2)
    )
  
  slope_plot_list[[i]] <- slope_plot
  ggsave(paste0("figure/rcs/SLOPE_", current_status, ".png"), slope_plot, 
         width = 6, height = 5, dpi = 300)
}
}

#Optimal cut-off value
{
data_cut=data
data_cut$status=ifelse(rowSums(data_ICD10[,statuses])==0,0,1)
data_cut=data_cut[rowSums(data_ICD10[, times] > 0) == length(times), ]

model <- glm(status ~ IPFD_ori, data = data_cut, family = binomial)

predicted_prob <- predict(model, type = "response")
roc_obj <- roc(data_cut$status, predicted_prob)
auc_value <- auc(roc_obj)
best <- coords(roc_obj,
               x    = "best", 
               input  = "threshold",
               best.method = "youden",
               ret  = c("threshold","sensitivity","specificity","youden"))
#youden’s index=sensitivity + specificity-1
#logit(P) = β₀ + β₁ × IPFD
model.out=summary(model)
b0=model.out$coefficients[1,1]
b1=model.out$coefficients[2,1]
IPFD_cutoff = (logit(best$threshold) - b0) / b1

#bootstrap
data_cut = data
data_cut$status = ifelse(rowSums(data_ICD10[, statuses]) == 0, 0, 1)
data_cut = data_cut[rowSums(data_ICD10[, times] > 0) == length(times), ]


boot_cutoff <- function(df, indices) {
  d <- df[indices, , drop = FALSE]
  m <- glm(status ~ IPFD_ori, data = d, family = binomial)
  
  p <- predict(m, type = "response")
  roc_obj <- roc(d$status, p, quiet = TRUE)
  
  th_prob <- as.numeric(
    coords(roc_obj,
           x           = "best",
           input       = "threshold",
           best.method = "youden",
           ret         = "threshold")
  )
  if (length(th_prob) != 1 || is.na(th_prob)) return(NA_real_)
  
  b0 <- coef(m)[1]
  b1 <- coef(m)[2]
  ipfd_cut <- (qlogis(th_prob) - b0) / b1
  return(ipfd_cut)
}

set.seed(2025)
boot_res <- boot(data     = data_cut,
                 statistic= boot_cutoff,
                 R        = 1000)

point_est <- boot_res$t0
ci_bca<- boot.ci(boot_res, type = "bca")$bca[4:5]
cat(sprintf("point estiamtion = %.3f\n95%% CI（percentile）= [%.3f, %.3f]\n95%% CI（BCa）= [%.3f, %.3f]\n",
            point_est,
            ci_perc[1], ci_perc[2],
            ci_bca[1],  ci_bca[2]))
# point estiamtion = 10.755
# 95% CI（BCa）= [8.045, 12.502]
data_cut$IPFD_binary <- ifelse(data_cut$IPFD_ori >= best_cutoff, 1, 0)

#Youden' index plot
roc_obj <- roc(data_cut$status, data_cut$IPFD_ori, quiet=TRUE)

roc_df <- coords(roc_obj,
                 x         = "all",
                 input     = "threshold",
                 ret       = c("threshold", "sensitivity", "specificity"),
                 transpose = FALSE)

roc_df$youden <- roc_df$sensitivity + roc_df$specificity - 1

best_row <- roc_df[which.max(roc_df$youden), ]

p=ggplot(roc_df, aes(x = threshold, y = youden)) +
  geom_line(size = 0.5) +
  geom_point(data = best_row, aes(x = threshold, y = youden),
             color = "darkred", size = 2) +
  geom_vline(xintercept = best_row$threshold, linetype = "dashed", color = "darkred") +
  geom_hline(yintercept = best_row$youden,   linetype = "dashed", color = "darkred") +
  annotate("text",
           x = best_row$threshold+15, 
           y = best_row$youden*0.9,
           label = sprintf("Optimal cut-off = %.2f\nMax Youden's index = %.2f",
                           best_row$threshold, best_row$youden),color = "black",
           size=7) +
  labs(title = "",
       x = "IPFD cut-off values (%)",
       y = "Youden's index (sensitivity + specificity − 1)") +
  theme_classic()+
  theme(
    axis.title = element_text(size = 15),
    axis.text = element_text(size = 15),
    #panel.grid.major = element_line(color = "grey90", size = 0.3),
    #panel.grid.minor = element_blank(),
    #panel.background = element_rect(fill = "white", color = NA),
    #plot.background = element_rect(fill = "white", color = NA),
    legend.position = "none"
  )

ggsave("figure/Youden.png", p, width = 10, height = 8, dpi = 300)

}

#MR
{
rm(list = ls())
library(TwoSampleMR)
library(forestploter)
library(grid)
library(ieugwasr)

#IPFD→diseases
exposure<- extract_instruments(outcomes='ebi-a-GCST90016675')
#load table maching diseases and GWAS id
finngen<-fread('data/outcome_ieu_fin.csv')
res_all<-NULL
res<-NULL
for (i in 1:length(finngen$disease)){
  outcome<-extract_outcome_data(snps = exposure$SNP ,outcomes =finngen$id[i] )
  if (is.null(outcome)){
    print(i)
    next
  }
  dat<-harmonise_data(exposure_dat = exposure,outcome_dat = outcome)
  if (nrow(subset(dat,dat$mr_keep ==TRUE))==0){
    next
  }
  heterogeneity <- mr_heterogeneity(dat)
  if (heterogeneity[1,8]<0.05){
    method=c('mr_ivw_mre')
  } else {
    method=c('mr_ivw_fe')
  }
  res<-generate_odds_ratios(mr_res = mr(dat,method_list=method))
  res$heterogeneity<-heterogeneity[1,8]
  res$p_pleiotropy<-mr_pleiotropy_test(dat)[1,7]
  res$outcome=finngen$disease[i]
  res_all<-rbind(res_all,res)
}
res_all$p_adj<-p.adjust(res_all$pval,"BH")
res_all$`OR (95%)`<-paste0(round(res_all$or,2),' (',round(res_all$or_lci95,2),'-',round(res_all$or_uci95,2),')')
print<-res_all%>%
  transmute(Outcome=outcome,
            blank=NA,
            `OR (95%)`,
            `P value`=sprintf("%.3f", pval),
            `Adjusted P value`=sprintf("%.3f",p_adj),
            `P for heterogeneity test`=sprintf("%.3f",heterogeneity),
            `P for horizontal pleiotropy test`=sprintf("%.3f",p_pleiotropy),
            nSNP=nsnp,
            OR=or,
            CI5=or_lci95,
            CI95=or_uci95
  )
fwrite(print,'table/ipfd_ieu.csv')

#Diseases→IPFD
res_all<-NULL
res<-NULL
outcomes<-list()
exposures=list()

for (i in 1:length(finngen$disease)){
  if (i %in% c(12)) {
    exposure<- extract_instruments(outcomes =finngen$id[i],p1=5e-7)
  } else if (i %in% c(13)) {
    exposure<- extract_instruments(outcomes =finngen$id[i],p1=5e-6)
  } else {
    exposure<- extract_instruments(outcomes =finngen$id[i],p1=5e-8) 
  }
  if (nrow(exposure)<5 & i!=13 ){
    exposure<- extract_instruments(outcomes =finngen$id[i],p1=5e-7)
  }
  if (nrow(exposure)<5){
    exposure<- extract_instruments(outcomes =finngen$id[i],p1=5e-6)
  }
  
  exposures[[i]]=exposure
  outcome<-read_outcome_data(filename = 'data/pdff.pancreas.tsv',
                             snps=exposure$SNP,
                             sep = '\t',
                             snp_col = 'variant_id',
                             beta_col = 'beta',
                             se_col = 'standard_error',
                             effect_allele_col = 'effect_allele',
                             other_allele_col = 'other_allele',
                             pval_col = 'p_value')
  if (is.null(outcome)){
    print(i)
    next
  }
  outcomes[[i]]<-outcome
  dat<-harmonise_data(exposure_dat = exposure,outcome_dat = outcome)
  if (nrow(subset(dat,dat$mr_keep ==TRUE))==0){
    next
  }
  heterogeneity <- mr_heterogeneity(dat)
  if (heterogeneity[1,8]<0.05){
    method=c('mr_ivw_mre')
  } else {
    method=c('mr_ivw_fe')
  }
  res<-generate_odds_ratios(mr_res = mr(dat,method_list=method))
  
  res$heterogeneity<-heterogeneity[1,8]
  res$p_pleiotropy<-mr_pleiotropy_test(dat)[1,7]
  res$outcome<-finngen$disease[i]
  res_all<-rbind(res_all,res)
  #f<-get_f(dat)
  #f_all<-rbind(f_all,f[,c('outcome','SNP','mr_keep','R2','F')])
}
res_all$p_adj<-p.adjust(res_all$pval,"BH")
res_all$`OR (95%)`<-paste0(round(res_all$or,2),' (',round(res_all$or_lci95,2),'-',round(res_all$or_uci95,2),')')
print<-res_all%>%
  transmute(Exposure=outcome,
            blank=NA,
            `OR (95%)`,
            `P value`=sprintf("%.3f", pval),
            `Adjusted P value`=sprintf("%.3f",p_adj),
            `P for heterogeneity test`=sprintf("%.3f",heterogeneity),
            `P for horizontal pleiotropy test`=sprintf("%.3f",p_pleiotropy),
            nSNP=nsnp,
            OR=or,
            CI5=or_lci95,
            CI95=or_uci95
  )
fwrite(print,'table/ipfd_ieu_rev.csv')

#Forest plot
pdata<-fread('table/ipfd_ieu.csv')
pdata<-mutate_at(pdata,c("blank"),~replace(.,is.na(.),''))
colnames(pdata)[grep('blank',colnames(pdata))]<-'                '
p_ori<- forest(pdata[,c(1:8)],
               est = pdata$OR,       
               lower = pdata$CI5,     
               ci_column = 2,   
               ref_line = 1,
               xlim = c(0, 2),
               theme = forest_theme(refline_lwd = 1.5,refline_col = 'red')
)
ggsave(paste0("figure/IPFD-ieu-ori", ".png"), p_ori, 
       width = 14, height = 4, dpi = 300)

pdata<-fread('table/ipfd_ieu_rev.csv')
pdata<-mutate_at(pdata,c("blank"),~replace(.,is.na(.),''))
pdata<-mutate_at(pdata,c("blank","P value"),~as.character(.))
colnames(pdata)[grep('blank',colnames(pdata))]<-'                '
p_rev<- forest(pdata[,c(1:8)],
               est = pdata$OR,       
               lower = pdata$CI5,     
               upper = pdata$CI95,      
               ci_column = 2,  
               ref_line = 1,
               xlim = c(0.5, 1.5),
               theme = forest_theme(refline_lwd = 1.5,refline_col = 'red'),
               ticks_at = c(0.5, 1, 1.5)
)
ggsave(paste0("figure/IPFD-ieu-rev", ".png"), p_rev, 
       width = 14, height = 4, dpi = 300)

#Leave-one-out

pdata<-fread('table/ipfd_ieu.csv')
exposure <- extract_instruments(outcomes = 'ebi-a-GCST90016675')
finngen <- fread('data/outcome_ieu_fin.csv')
p_leave1=list()

for (i in which(pdata$`Adjusted P value`<0.05)) {
  outcome <- extract_outcome_data(snps = exposure$SNP, outcomes = finngen$id[i])
  if (is.null(outcome)){
    print(i)
    next
  }
  dat<-harmonise_data(exposure_dat = exposure,outcome_dat = outcome)
  dat$exposure<-'IPFD'
  dat$outcome<-finngen$disease[i]
  heterogeneity <- mr_heterogeneity(dat)
  if (heterogeneity[1,8]<0.05){
    p<-mr_leaveoneout_plot(leaveoneout_results = mr_leaveoneout(dat,method = mr_ivw_mre))
  } else {
    p<-mr_leaveoneout_plot(leaveoneout_results = mr_leaveoneout(dat,method = mr_ivw_fe))
  }
  p<-mr_leaveoneout_plot(leaveoneout_results = mr_leaveoneout(dat,method = mr_ivw))
  p_leave1[[i]]<-p
  png(filename =paste0("figure/leave1/loo_",finngen$id[i],".png"),
      width = 9, height = 6, units = 'cm',res=300
  )
  print(p)
  dev.off()
}
p_leave1[which(pdata$`Adjusted P value`<0.05)]
}

