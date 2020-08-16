(* Title:      Quadcopter Controller Verification - Verification Framework for Control System 
                                                    Functionality of Unmanned Aerial Vehicles
   Author:     Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk>
   Maintainer: Omar A. Jasim <oajasim1@sheffield.ac.uk>, Sandor M. Veres <s.veres@sheffield.ac.uk> 
*)

theory Quadrotor_Veri
imports  Complex_Main 
"Quaternions.Quaternions"
(*"~~/src/HOL/Probability/Probability"*)
"~~/src/HOL/Matrix_LP/Matrix"
"~~/src/HOL/Library/Function_Algebras"
(*"~~/src/HOL/Analysis/Analysis"*)
(*"~~/src/HOL/Analysis/Finite_Cartesian_Product"*)
begin
sledgehammer_params [provers = cvc4 z3 spass e remote_vampire , smt_proofs=true]

(**************************************************************************************************)
text \<open>Time definition\<close>
(**************************************************************************************************)
definition T :: "real set"
  where "T ={t. t\<in>{0..\<infinity>} }" 

(**************************************************************************************************)
text \<open>Definitions of sets, positive-definite matrix, and positive-definite symmetric matrix\<close>
(**************************************************************************************************)
definition D3_vec_set :: "(real, 3) vec set"
  where "D3_vec_set ={d. (\<forall>i.\<forall>f.\<forall>t\<in>T.  d$i = f t)}"  

definition D6_vec_set :: "(real, 6) vec set"
  where "D6_vec_set ={a. (\<forall>i.\<forall>f.\<forall>t\<in>T.  a$i = f t)}" 

(*positive-definite matrix*)
definition "pos_def_3x3_matrix X = (\<exists>r. \<exists>M. M=X \<and> (r:: (real,3) vec) \<noteq>0 \<and> (r \<bullet> (M *v r))>0)"

definition "pos_def_6x6_matrix Y = (\<exists>r. \<exists>F. F=Y \<and> (r:: (real,6) vec) \<noteq>0 \<and> (r \<bullet> (F *v r))>0)"

(*from Sylvester theorem : a matrix is a positive definite and symmetric matrix iff its principle 
  minors is positive or its eginvalues are positive*)  
definition "pos_def_symmetric_matrix A = (pos_def_6x6_matrix A \<and> A = transpose(A) \<and> det(A)\<noteq>0  
      \<and> (A$1$1)>0 \<and> ((A$1$1)*(A$2$2) - (A$1$2)*(A$2$1))>0 \<and> 
      (\<exists>!(B:: ((real,3) vec,3) vec). B$1$1=A$1$1 \<and> B$2$1=A$2$1 \<and> B$3$1=A$3$1 \<and> B$1$2=A$1$2 \<and> 
      B$2$2=A$2$2 \<and> B$3$2=A$3$2 \<and> B$1$3=A$1$3 \<and> B$2$3=A$2$3  \<and> B$3$3=A$3$3 \<and> det(B)>0 )   \<and>
      (\<exists>!(C:: ((real,4) vec,4) vec). C$1$1=A$1$1 \<and> C$2$1=A$2$1 \<and> C$3$1=A$3$1 \<and> C$4$1=A$4$1 \<and> 
      C$1$2=A$1$2 \<and> C$2$2=A$2$2 \<and> C$3$2=A$3$2 \<and>  C$4$2=A$4$2 \<and> C$1$3=A$1$3 \<and> C$2$3=A$2$3  \<and> 
      C$3$3=A$3$3 \<and> C$4$3=A$4$3 \<and> C$1$4=A$1$4 \<and> C$2$4=A$2$4 \<and> C$3$4=A$3$4 \<and> C$4$4=A$4$4 \<and> 
      det(C)>0 ) \<and>  (\<exists>!(D:: ((real,5) vec,5) vec). D$1$1=A$1$1 \<and> D$2$1=A$2$1 \<and> D$3$1=A$3$1 \<and> 
      D$4$1=A$4$1 \<and> D$5$1=A$5$1 \<and> D$1$2=A$1$2 \<and> D$2$2=A$2$2 \<and> D$3$2=A$3$2 \<and> D$4$2=A$4$2 \<and>  
      D$5$2=A$5$2 \<and> D$1$3=A$1$3 \<and> D$2$3=A$2$3 \<and> D$3$3=A$3$3 \<and> D$4$3=A$4$3 \<and> D$5$3=A$5$3 \<and> 
      D$1$4=A$1$4 \<and> D$2$4=A$2$4 \<and> D$3$4=A$3$4 \<and> D$4$4=A$4$4 \<and> D$5$4=A$5$4 \<and> D$1$5=A$1$5 \<and> 
      D$2$5=A$2$5 \<and> D$3$5=A$3$5 \<and> D$4$5=A$4$5 \<and> D$5$5=A$5$5 \<and> det(D)>0 )  \<and> det(A)>0 )"

(**************************************************************************************************)
text \<open>Parameters definitions\<close>
(**************************************************************************************************)
definition"(ell :: real)=0.2" (*m*)    (*arm length*) 
definition"(b :: real)=0.00000012" (*N.m/(rad/sec)\<^sup>2*)
definition"(l :: real)=0.000009" (*N/(rad/sec)\<^sup>2*)
definition"(\<alpha> :: real)=180.7904" 
definition"(\<sigma> :: real)=36.3458" 
definition"(\<delta> :: real)=0.0477" 
definition"(\<beta> :: real)=0.3675"
definition"(\<gamma> :: real)=0.4231"
definition"(\<mu> :: real)=0.0095"
definition"(\<rho> :: real)=36.3485"
definition"(\<II>\<^sub>m\<^sub>i\<^sub>n :: real)=155.88" (*\<II> instead of \<lambda> as the \<lambda> symbol is reserved*)
definition"(\<II>\<^sub>m\<^sub>a\<^sub>x :: real)=171.5" (*\<II> instead of \<lambda> as the \<lambda> symbol is reserved*)
definition"(\<Omega>\<^sub>m\<^sub>a\<^sub>x :: real)=707.1068" (*rad/sec*)
definition"(k\<^sub>q\<^sub>0 :: real)=0.01" 

(**************************************************************************************************)
text \<open>Matrices definitions\<close>
(**************************************************************************************************)
(* I uncertain inertia matrix *)
definition "I_mat I = (\<forall> matrix_inv(I). pos_def_3x3_matrix I \<and> invertible I \<and> transpose I = I \<and> 
                          I**matrix_inv(I) = mat 1 \<and> norm(matrix_inv(I)) > 0 \<and> 
                       \<II>\<^sub>m\<^sub>i\<^sub>n \<le> norm(matrix_inv(I)) \<and> norm(matrix_inv(I)) \<le> \<II>\<^sub>m\<^sub>a\<^sub>x)"

(* I\<^sub>h\<^sub>a\<^sub>t the assumed inertia matrix values*)
definition "I\<^sub>h\<^sub>a\<^sub>t_mat (I\<^sub>h\<^sub>a\<^sub>t :: ((real, 3) vec, 3) vec) = (pos_def_3x3_matrix I\<^sub>h\<^sub>a\<^sub>t 
                     \<and> transpose I\<^sub>h\<^sub>a\<^sub>t = I\<^sub>h\<^sub>a\<^sub>t \<and> invertible I\<^sub>h\<^sub>a\<^sub>t \<and>
                     I\<^sub>h\<^sub>a\<^sub>t$1$1 = 0.005831 \<and> I\<^sub>h\<^sub>a\<^sub>t$2$1 = 0         \<and> I\<^sub>h\<^sub>a\<^sub>t$3$1 = 0 \<and>
                     I\<^sub>h\<^sub>a\<^sub>t$1$2 = 0        \<and> I\<^sub>h\<^sub>a\<^sub>t$2$2 = 0.005831  \<and> I\<^sub>h\<^sub>a\<^sub>t$3$2 = 0 \<and>
                     I\<^sub>h\<^sub>a\<^sub>t$1$3 = 0        \<and> I\<^sub>h\<^sub>a\<^sub>t$2$3 = 0         \<and> I\<^sub>h\<^sub>a\<^sub>t$3$3 = 0.01166)"

(* \<Gamma> cross product matrix values*)
definition "\<Gamma>_mat (\<Gamma> :: ((real, 3) vec, 3) vec) \<omega>  = (pos_def_3x3_matrix \<Gamma> \<and>
                   \<Gamma>$1$1 = 0   \<and> \<Gamma>$2$1 =-\<omega>$3 \<and> \<Gamma>$3$1 = \<omega>$2 \<and>
                   \<Gamma>$1$2 = \<omega>$3 \<and> \<Gamma>$2$2 = 0   \<and> \<Gamma>$3$2 =-\<omega>$1 \<and>
                   \<Gamma>$1$3 =-\<omega>$2 \<and> \<Gamma>$2$3 = \<omega>$1 \<and> \<Gamma>$3$3 = 0   )"

(* K\<^sub>q matrix values*)
definition "K\<^sub>q_mat (K\<^sub>q :: ((real, 3) vec, 3) vec)  = (pos_def_3x3_matrix K\<^sub>q \<and>
                   K\<^sub>q$1$1 = 16 \<and> K\<^sub>q$2$1 = 0   \<and> K\<^sub>q$3$1 = 0 \<and>
                   K\<^sub>q$1$2 = 0  \<and> K\<^sub>q$2$2 = 16  \<and> K\<^sub>q$3$2 = 0 \<and>
                   K\<^sub>q$1$3 = 0  \<and> K\<^sub>q$2$3 = 0   \<and> K\<^sub>q$3$3 = 25)"

(* K\<^sub>\<omega> matrix values*)
definition "K\<^sub>\<omega>_mat (K\<^sub>\<omega> :: ((real, 3) vec, 3) vec)  = (pos_def_3x3_matrix K\<^sub>\<omega> \<and> 
                   K\<^sub>\<omega>$1$1 = 0.9  \<and> K\<^sub>\<omega>$2$1 = 0   \<and> K\<^sub>\<omega>$3$1 = 0 \<and>
                   K\<^sub>\<omega>$1$2 = 0    \<and> K\<^sub>\<omega>$2$2 = 0.9 \<and> K\<^sub>\<omega>$3$2 = 0 \<and>
                   K\<^sub>\<omega>$1$3 = 0    \<and> K\<^sub>\<omega>$2$3 = 0   \<and> K\<^sub>\<omega>$3$3 = 0.0064)"

(* Z\<^sub>t\<^sub>i\<^sub>l\<^sub>d\<^sub>e matrix values ** note: quaternion sequence is different from the paper since: 
q\<^sub>0 == q$1, q\<^sub>1 == q$2, q\<^sub>2 == q$3, q\<^sub>3 == q$4 *)
definition "Z\<^sub>t_mat (Z\<^sub>t ::((real, 4)vec,3)vec) q  = 
            (Z\<^sub>t$1$1=2*-Im1 q  \<and>  Z\<^sub>t$2$1=2*  Re q \<and>  Z\<^sub>t$3$1=2* Im3 q \<and> Z\<^sub>t$4$1=2*-Im2 q \<and>   
             Z\<^sub>t$1$2=2*-Im2 q  \<and>  Z\<^sub>t$2$2=2*-Im3 q \<and>  Z\<^sub>t$3$2=2*  Re q \<and> Z\<^sub>t$4$2=2* Im1 q \<and>   
             Z\<^sub>t$1$3=2*-Im3 q  \<and>  Z\<^sub>t$2$3=2* Im2 q \<and>  Z\<^sub>t$3$3=2*-Im1 q \<and> Z\<^sub>t$4$3=2*  Re q )"

(* A matrix values*)
definition "A_mat (A :: ((real, 6) vec,6) vec)  = 
            (A$1$1=0    \<and>  A$2$1=0   \<and>  A$3$1=0   \<and>  A$4$1=1    \<and>  A$5$1=0    \<and>  A$6$1=0 \<and>
             A$1$2=0    \<and>  A$2$2=0   \<and>  A$3$2=0   \<and>  A$4$2=0    \<and>  A$5$2=1    \<and>  A$6$2=0 \<and>
             A$1$3=0    \<and>  A$2$3=0   \<and>  A$3$3=0   \<and>  A$4$3=0    \<and>  A$5$3=0    \<and>  A$6$3=1 \<and>
             A$1$4=-16  \<and>  A$2$4=0   \<and>  A$3$4=0   \<and>  A$4$4=-0.9 \<and>  A$5$4=0    \<and>  A$6$4=0 \<and>
             A$1$5=0    \<and>  A$2$5=-16 \<and>  A$3$5=0   \<and>  A$4$5=0    \<and>  A$5$5=-0.9 \<and>  A$6$5=0 \<and>
             A$1$6=0    \<and>  A$2$6=0   \<and>  A$3$6=-25 \<and>  A$4$6=0    \<and>  A$5$6=0    \<and>  A$6$6=-0.0064 )"

(* G matrix values*)
definition "G_mat (G :: ((real, 3) vec, 6) vec)  = 
            (G$1$1=0     \<and>  G$2$1=0     \<and>  G$3$1=0 \<and>    
             G$1$2=0     \<and>  G$2$2=0     \<and>  G$3$2=0 \<and>    
             G$1$3=0     \<and>  G$2$3=0     \<and>  G$3$3=0 \<and>    
             G$1$4=1     \<and>  G$2$4=0     \<and>  G$3$4=0 \<and>    
             G$1$5=0     \<and>  G$2$5=1     \<and>  G$3$5=0 \<and>    
             G$1$6=0     \<and>  G$2$6=0     \<and>  G$3$6=1 )"

(* P matrix values*)
definition "P_mat (P :: ((real, 6) vec,6) vec)  = (pos_def_symmetric_matrix P \<and>
             P$1$1 = 0.000000000009 \<and>  P$2$1=0              \<and>  P$3$1=0               \<and>  P$4$1=0            \<and>  P$5$1=0            \<and>  P$6$1=0 \<and>
             P$1$2 = 0              \<and>  P$2$2=0.000000000009 \<and>  P$3$2=0               \<and>  P$4$2=0            \<and>  P$5$2=0            \<and>  P$6$2=0 \<and>
             P$1$3 = 0              \<and>  P$2$3=0              \<and>  P$3$3=0.0000000000005 \<and>  P$4$3=0            \<and>  P$5$3=0            \<and>  P$6$3=0 \<and>
             P$1$4 = 0              \<and>  P$2$4=0              \<and>  P$3$4=0               \<and>  P$4$4=0.0000000003 \<and>  P$5$4=0            \<and>  P$6$4=0 \<and>
             P$1$5 = 0              \<and>  P$2$5=0              \<and>  P$3$5=0               \<and>  P$4$5=0            \<and>  P$5$5=0.0000000003 \<and>  P$6$5=0 \<and>
             P$1$6 = 0              \<and>  P$2$6=0              \<and>  P$3$6=0               \<and>  P$4$6=0            \<and>  P$5$6=0            \<and>  P$6$6=0.0000000008 )"

(* Q matrix values*)
definition "Q_mat (Q :: ((real, 6) vec,6) vec)  = (pos_def_symmetric_matrix Q \<and>
             Q$1$1 = 0.00000000001566 \<and>  Q$2$1= 0                \<and>  Q$3$1= 0                \<and>  Q$4$1=-0.0000000000045 \<and>  Q$5$1= 0               \<and>  Q$6$1=0                 \<and>
             Q$1$2 = 0                \<and>  Q$2$2= 0.00000000001566 \<and>  Q$3$2= 0                \<and>  Q$4$2= 0               \<and>  Q$5$2=-0.0000000000045 \<and>  Q$6$2=0                 \<and>
             Q$1$3 = 0                \<and>  Q$2$3= 0                \<and>  Q$3$3= 0.000000002539   \<and>  Q$4$3= 0               \<and>  Q$5$3= 0               \<and>  Q$6$3=-0.00000000000025 \<and>
             Q$1$4 =-0.0000000000045  \<and>  Q$2$4= 0                \<and>  Q$3$4= 0                \<and>  Q$4$4= 0.0000000002466 \<and>  Q$5$4= 0               \<and>  Q$6$4=0                 \<and>
             Q$1$5 = 0                \<and>  Q$2$5=-0.0000000000045  \<and>  Q$3$5= 0                \<and>  Q$4$5= 0               \<and>  Q$5$5= 0.0000000002466 \<and>  Q$6$5=0                 \<and>
             Q$1$6 = 0                \<and>  Q$2$6= 0                \<and>  Q$3$6=-0.00000000000025 \<and>  Q$4$6= 0               \<and>  Q$5$6= 0               \<and>  Q$6$6=0.00000006347     )"
(*################################################################################################*)

(**************************************************************************************************)
section \<open>Quadcopter attitude dynamics\<close>
(**************************************************************************************************)

(* \<tau> vector Eq (10) *)
definition "torq_fun \<tau> = ((\<exists> \<Omega>\<^sub>1 \<Omega>\<^sub>2 \<Omega>\<^sub>3 \<Omega>\<^sub>4. \<bar>\<Omega>\<^sub>1\<bar><\<Omega>\<^sub>m\<^sub>a\<^sub>x \<and> \<bar>\<Omega>\<^sub>2\<bar><\<Omega>\<^sub>m\<^sub>a\<^sub>x \<and> 
                         \<bar>\<Omega>\<^sub>3\<bar><\<Omega>\<^sub>m\<^sub>a\<^sub>x \<and> \<bar>\<Omega>\<^sub>4\<bar><\<Omega>\<^sub>m\<^sub>a\<^sub>x \<and> \<tau> \<in> D3_vec_set \<and> 
                         \<tau>$1= ell*l*(\<Omega>\<^sub>2\<^sup>2 - \<Omega>\<^sub>4\<^sup>2)  \<and>
                         \<tau>$2= ell*l*(-\<Omega>\<^sub>1\<^sup>2 + \<Omega>\<^sub>3\<^sup>2) \<and>
                         \<tau>$3= b*(-\<Omega>\<^sub>1\<^sup>2 + \<Omega>\<^sub>2\<^sup>2 - \<Omega>\<^sub>3\<^sup>2 + \<Omega>\<^sub>4\<^sup>2) ))"

(* C vector equation *)
definition "C_fun C \<Gamma> I (\<omega> :: (real,3) vec) = (\<Gamma>_mat \<Gamma>  \<omega> \<and> C = \<Gamma> *v (I *v \<omega>))" 

(* attitude dynamics Eq (9) *)
definition "att_dyms \<omega> \<omega>' I C \<Gamma> \<tau> \<tau>\<^sub>d = (\<forall>t\<in>T. (\<forall>\<omega>. \<omega>\<in>D3_vec_set) \<and> 
                     (\<forall>i.((\<lambda>t. \<omega>$i) has_derivative (\<lambda>t. \<omega>'$i)) (at t within T)) \<and> 
                     I_mat I \<and> C_fun C \<Gamma> I \<omega> \<and> \<tau> = I *v \<omega>' + C + \<tau>\<^sub>d)"
(*################################################################################################*)

(**************************************************************************************************)
section \<open>Control System Design\<close>
(**************************************************************************************************)
(*general definition to transfer quaternions form "Quaternions.thy" theory to a 4X1 real_vector*)
definition quat_to_vec :: "quat \<Rightarrow> (real,4) vec" where
  "quat_to_vec a \<equiv> vector[Re a, Im1 a, Im2 a, Im3 a]"

(*quaternion error q\<^sub>e = q\<^sub>r \<otimes> q\<^sup>*. Note: the sequence here of q\<^sub>0 and q\<^sub>r\<^sub>0 start as q$1 and q\<^sub>r$1 respectively, Eq (19)*)
definition "quat_error (q\<^sub>e ::quat) (q\<^sub>r ::quat) (q ::quat) = (
   Re q\<^sub>e = (Re q\<^sub>r* Re q)+(Im1 q\<^sub>r*Im1 q)+(Im2 q\<^sub>r*Im2 q)+(Im3 q\<^sub>r*Im3 q) \<and>
  Im1 q\<^sub>e =-(Re q\<^sub>r*Im1 q)+(Im1 q\<^sub>r* Re q)+(Im3 q\<^sub>r*Im2 q)-(Im2 q\<^sub>r*Im3 q) \<and>
  Im2 q\<^sub>e =-(Re q\<^sub>r*Im2 q)+(Im2 q\<^sub>r* Re q)+(Im1 q\<^sub>r*Im3 q)-(Im3 q\<^sub>r*Im1 q) \<and> 
  Im3 q\<^sub>e =-(Re q\<^sub>r*Im3 q)+(Im3 q\<^sub>r* Re q)+(Im2 q\<^sub>r*Im1 q)-(Im1 q\<^sub>r*Im2 q) )"

(*error \<xi> definition Eq (21)*)
definition "error_fun (\<xi> :: (real,3) vec) q\<^sub>e = (
  \<xi>$1 = Im1 q\<^sub>e \<and>
  \<xi>$2 = Im2 q\<^sub>e \<and>
  \<xi>$3 = Im3 q\<^sub>e )"

(*\dot{q\<^sub>r} definition Eq (22)*)
definition "dot_q\<^sub>r_fun q\<^sub>r' q\<^sub>e K\<^sub>q \<xi> = (
  Re q\<^sub>r' =  k\<^sub>q\<^sub>0 * Re q\<^sub>e \<and> 
 Im1 q\<^sub>r' = (K\<^sub>q *v \<xi>)$1  \<and>       
 Im2 q\<^sub>r' = (K\<^sub>q *v \<xi>)$2  \<and> 
 Im3 q\<^sub>r' = (K\<^sub>q *v \<xi>)$3 )"

(*\dot{\<xi>} definition Eq (23)*)
definition "dot_error_fun (\<xi>' :: (real,3) vec) q' q\<^sub>r' \<omega> \<omega>\<^sub>r\<^sub>e\<^sub>f Z\<^sub>t =
(\<omega>\<^sub>r\<^sub>e\<^sub>f =Z\<^sub>t*v  quat_to_vec q\<^sub>r' \<and> \<omega> = Z\<^sub>t*v q' \<and> \<xi>' = Z\<^sub>t*v quat_to_vec q\<^sub>r' - \<omega>)"                   

(*\ddot{\<xi>} definition *)
definition "ddot_error_fun (\<xi>'' :: (real,3) vec) \<xi>' \<omega>' \<omega>'\<^sub>r\<^sub>e\<^sub>f = (\<forall>t\<in>T. 
 (\<forall>i.((\<lambda>t. \<xi>'$i) has_derivative (\<lambda>t. \<xi>''$i)) (at t within T)) \<and> \<xi>'' = \<omega>'\<^sub>r\<^sub>e\<^sub>f - \<omega>')"

(* \<eta> vector definition*)
definition "\<eta>_vec (\<eta>:: (real,6)vec) \<xi> \<xi>' = (\<eta>$1 = \<xi>$1  \<and> \<eta>$2 = \<xi>$2  \<and> \<eta>$3 = \<xi>$3  \<and>
                                           \<eta>$4 = \<xi>'$1 \<and> \<eta>$5 = \<xi>'$2 \<and> \<eta>$6 = \<xi>'$3 )"

(*################################################################################################*)

(**************************************************************************************************)
subsection \<open>Controller definitions\<close>
(**************************************************************************************************)

(* desired angular velocity derivative *)
definition "dot_ang_vel \<omega>\<^sub>r\<^sub>e\<^sub>f \<omega>'\<^sub>r\<^sub>e\<^sub>f = (\<forall>t\<in>T. \<forall>i.((\<lambda>t. \<omega>\<^sub>r\<^sub>e\<^sub>f$i) has_derivative (\<lambda>t. \<omega>'\<^sub>r\<^sub>e\<^sub>f$i)) (at t within T))"

(* u control input definition Eq (25) *)
definition "cont_u_def (u :: (real, 3) vec) \<omega>'\<^sub>r\<^sub>e\<^sub>f K\<^sub>\<omega> K\<^sub>q \<xi>' \<xi>  = (u= \<omega>'\<^sub>r\<^sub>e\<^sub>f + K\<^sub>\<omega> *v \<xi>' + K\<^sub>q *v \<xi>)"

(*y equation (27) *)
definition "y_eq y u I I\<^sub>h\<^sub>a\<^sub>t \<Delta> \<tau>\<^sub>d = (y = (mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(I)*v (\<Delta>-\<tau>\<^sub>d))"

(* \<zeta> term definition Eq (44) *)
definition "zeta_def \<zeta> (y::(real,3)vec) = (\<forall>t\<in>T.\<exists>\<epsilon>. \<epsilon>>0 \<and> norm(y)\<le>\<epsilon> \<longrightarrow> \<zeta> \<ge> \<epsilon>/\<II>\<^sub>m\<^sub>i\<^sub>n)"

(* u\<^sub>d term definition Eq (42) *)
definition "u\<^sub>d_def u\<^sub>d G Q \<zeta> \<eta> = (\<forall>t\<in>T. 
    if (norm (transpose (G) *v (Q*v \<eta>)) \<ge> \<mu>) 
    then (u\<^sub>d = (\<zeta>/norm(transpose (G) *v (Q*v \<eta>))) *s (transpose (G) *v (Q*v \<eta>))) 
    else (u\<^sub>d = (\<zeta>/\<mu>) *s (transpose (G) *v (Q*v \<eta>))))"

(* C\<^sub>h\<^sub>a\<^sub>t equation *)
definition "C\<^sub>h\<^sub>a\<^sub>t_fun C\<^sub>h\<^sub>a\<^sub>t \<Gamma> I\<^sub>h\<^sub>a\<^sub>t \<omega> = (\<Gamma>_mat \<Gamma> \<omega> \<and> C\<^sub>h\<^sub>a\<^sub>t = \<Gamma> *v (I\<^sub>h\<^sub>a\<^sub>t *v \<omega>))"

(* Attitude control law Eq (18) *)
definition "cont_law (\<tau> :: (real, 3) vec) I\<^sub>h\<^sub>a\<^sub>t u u\<^sub>d C\<^sub>h\<^sub>a\<^sub>t = (\<tau> = I\<^sub>h\<^sub>a\<^sub>t *v u + u\<^sub>d + C\<^sub>h\<^sub>a\<^sub>t)"

(*################################################################################################*)

(**************************************************************************************************)
subsection \<open>assumptions\<close>
(**************************************************************************************************)

(* assumption 1,  Eq (31)*)
definition "assump1 \<omega>'\<^sub>r\<^sub>e\<^sub>f = ((SUP t:T. norm(\<omega>'\<^sub>r\<^sub>e\<^sub>f)) < \<alpha>)"

(* assumption 2, Eq (32-33) *)
definition "assump2 I I\<^sub>h\<^sub>a\<^sub>t = (I_mat I \<and> I\<^sub>h\<^sub>a\<^sub>t_mat I\<^sub>h\<^sub>a\<^sub>t \<and>
                        \<II>\<^sub>m\<^sub>i\<^sub>n \<le> norm(matrix_inv(I)) \<and> norm(matrix_inv(I)) \<le> \<II>\<^sub>m\<^sub>a\<^sub>x \<and>
                         norm(mat 1 - ((matrix_inv(I)) ** I\<^sub>h\<^sub>a\<^sub>t )) \<le> \<delta>)"

(* assumption 3, Eq (34) *)
definition "assump3 (\<tau>\<^sub>d ::(real,3)vec) = (norm(\<tau>\<^sub>d)\<le>\<gamma>)"

(* Lemma 1, Eq (35-37) *)
lemma Eqs_35__37:
  fixes \<Delta> :: "(real,3)vec" 
  assumes "att_dyms \<omega> \<omega>' I C \<Gamma> \<tau> \<tau>\<^sub>d" and "I_mat I" and "I\<^sub>h\<^sub>a\<^sub>t_mat I\<^sub>h\<^sub>a\<^sub>t" and "C_fun C \<Gamma> I \<omega>" 
      and "C\<^sub>h\<^sub>a\<^sub>t_fun C\<^sub>h\<^sub>a\<^sub>t \<Gamma> I\<^sub>h\<^sub>a\<^sub>t \<omega>"  and "\<Gamma>_mat \<Gamma> \<omega>" and "assump1 \<omega>'\<^sub>r\<^sub>e\<^sub>f" and "assump2 I I\<^sub>h\<^sub>a\<^sub>t" 
      and "norm(\<omega>)\<le>\<sigma>" and "\<Delta> = C\<^sub>h\<^sub>a\<^sub>t -C" and "norm(\<Gamma>)\<le> \<rho>" 
    shows "norm(\<Delta>) \<le> \<beta>" 
proof-
  have a1: "\<exists> \<Gamma>. C = \<Gamma> *v (I *v \<omega>)" 
    using assms(4) C_fun_def by auto
  have a2:"\<exists> \<Gamma>. C\<^sub>h\<^sub>a\<^sub>t = \<Gamma> *v (I\<^sub>h\<^sub>a\<^sub>t *v \<omega>)"   
    using assms(5) C\<^sub>h\<^sub>a\<^sub>t_fun_def  by blast
  from a1 a2 have "\<exists> \<Gamma>. \<Delta> = \<Gamma> *v (I\<^sub>h\<^sub>a\<^sub>t *v \<omega>)-\<Gamma> *v (I *v \<omega>)" 
    using C\<^sub>h\<^sub>a\<^sub>t_fun_def C_fun_def assms(4) assms(5) assms(10) by metis 
  then have "\<exists> \<Gamma>. \<Delta> = (\<Gamma> ** I\<^sub>h\<^sub>a\<^sub>t) *v \<omega> - (\<Gamma> ** I) *v \<omega> "
    using matrix_vector_mul_assoc by metis
  then have "\<exists> \<Gamma>. \<Delta> =  \<Gamma>**(I\<^sub>h\<^sub>a\<^sub>t- I)*v \<omega>"
    by (metis matrix_vector_mul_assoc matrix_vector_mult_diff_rdistrib vec.diff)
  then have "\<exists> \<Gamma>. \<Delta> =  (\<Gamma>**I\<^sub>h\<^sub>a\<^sub>t - \<Gamma>**I)*v \<omega>"
    using  matrix_vector_mul_assoc matrix_vector_mult_diff_rdistrib vec.diff by smt
  then have  "\<exists> \<Gamma>.  \<Delta> =  \<Gamma>**I\<^sub>h\<^sub>a\<^sub>t*v \<omega> -  \<Gamma>**I*v \<omega>"
    by (simp add: matrix_vector_mult_diff_rdistrib)
  then have  "\<exists> \<Gamma>. \<Delta>  = \<Gamma> *v (\<omega> v* transpose I\<^sub>h\<^sub>a\<^sub>t) -  \<Gamma> *v (\<omega> v* transpose I)"
    by (simp add: matrix_vector_mul_assoc)
  then have "\<exists> \<Gamma> matrix_inv(I). \<Delta>  = \<Gamma> *v (\<omega> v* I\<^sub>h\<^sub>a\<^sub>t) - \<Gamma> *v (\<omega> v* I)"
    using I_mat_def I\<^sub>h\<^sub>a\<^sub>t_mat_def assms(2) assms(3)  by metis
  then have "\<exists> \<Gamma> matrix_inv(I). \<Delta> v* matrix_inv(I)  = (\<Gamma> *v (\<omega> v* I\<^sub>h\<^sub>a\<^sub>t) - \<Gamma> *v (\<omega> v* I)) v* matrix_inv(I)"
    by auto
  then have "\<exists> \<Gamma> matrix_inv(I). \<Delta> v* matrix_inv(I)  = \<Gamma> *v (\<omega> v* I\<^sub>h\<^sub>a\<^sub>t)v* matrix_inv(I) - \<Gamma> *v (\<omega> v* I) v* matrix_inv(I)"
    by (metis Cartesian_Euclidean_Space.transpose_matrix_vector matrix_vector_mult_diff_distrib)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). \<Delta> v* matrix_inv(I)  = (\<omega> v* I\<^sub>h\<^sub>a\<^sub>t)v* (matrix_inv(I)**\<Gamma>) - \<Gamma> *v (\<omega> v* I) v* matrix_inv(I)"
    by (metis (no_types, hide_lams) Cartesian_Euclidean_Space.vector_matrix_mult_0_right cancel_comm_monoid_add_class.diff_cancel times0_left)
  then have x1: "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). \<Delta> v* matrix_inv(I)  = (\<omega> v* (I\<^sub>h\<^sub>a\<^sub>t**matrix_inv(I)))v* \<Gamma> - \<Gamma> *v (\<omega> v* I) v* matrix_inv(I)"
    by (metis (no_types, lifting) vector_matrix_mul_assoc) 
  have "\<exists> matrix_inv(I::((real, 3) vec, 3) vec). I**matrix_inv(I) = mat 1"   
    using  matrix_mul_rid by metis
  from this x1  have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). \<Delta> v* matrix_inv(I) = \<Gamma> *v (\<omega> v* I\<^sub>h\<^sub>a\<^sub>t) v* matrix_inv(I)- (\<omega> v* mat 1)v* \<Gamma>"
    by (metis Cartesian_Euclidean_Space.vector_matrix_mult_0_right diff_zero)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). \<Delta> v* matrix_inv(I) = (\<omega> v* I\<^sub>h\<^sub>a\<^sub>t) v* (matrix_inv(I)**\<Gamma>) - (\<omega> v* mat 1)v* \<Gamma> "
    by (metis (no_types, hide_lams) Cartesian_Euclidean_Space.vector_matrix_mult_0_right cancel_comm_monoid_add_class.diff_cancel times0_left)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). \<Delta> v* matrix_inv(I) = (\<omega> v* (I\<^sub>h\<^sub>a\<^sub>t**matrix_inv(I))) v* \<Gamma> -  (\<omega> v* mat 1)v* \<Gamma> "
    by (metis (no_types, lifting) vector_matrix_mul_assoc)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). \<Delta> v* matrix_inv(I) = (\<omega> v* (matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) v* \<Gamma> - (\<omega> v* mat 1)v* \<Gamma>"
    by (metis Cartesian_Euclidean_Space.vector_transpose_matrix diff_zero matrix_vector_mult_0)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). \<Delta> v* matrix_inv(I) = (\<omega> v*(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t - mat 1)) v* \<Gamma>"
    by (metis Cartesian_Euclidean_Space.transpose_matrix_vector matrix_vector_mult_0 Cartesian_Euclidean_Space.vector_transpose_matrix)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). norm( \<Delta> v* matrix_inv(I)) = norm( \<omega> v* -(mat 1 - matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t) v* \<Gamma>)"
    by (metis Cartesian_Euclidean_Space.vector_matrix_mult_0_right norm_zero times0_left)
 then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). norm(\<Delta>) * norm(matrix_inv(I)) = norm( \<omega> v* -(mat 1 - matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t) v* \<Gamma>)"
   by (metis Cartesian_Euclidean_Space.vector_matrix_mult_0_right diff_zero mult_zero_right norm_zero)
 then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). norm(\<Delta>) * norm(matrix_inv(I)) = norm( \<omega> v* -(mat 1 - matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) * norm \<Gamma>"
   by (metis mult_zero_right norm_zero)
 then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). norm \<Delta> * norm(matrix_inv(I)) = norm \<omega> * norm(-(mat 1 - matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) * norm \<Gamma>"
   by (metis (no_types, hide_lams) mult_zero_right norm_zero times0_left vector_space_over_itself.scale_scale)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). norm \<Delta> = (norm \<omega> * norm(-(mat 1 - matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) * norm \<Gamma>)/norm(matrix_inv(I))"
    using I_mat_def assms(2) by fastforce
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). norm \<Delta> \<le> (norm \<omega> * norm(-(mat 1 - matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) * norm \<Gamma>)/\<II>\<^sub>m\<^sub>a\<^sub>x"
    using assms by (metis (mono_tags, hide_lams) I_mat_def less_irrefl norm_zero)
  then have "\<exists> \<Gamma> matrix_inv(I::((real, 3) vec, 3) vec). norm \<Delta> \<le> (\<sigma> * \<delta> * \<rho>)/\<II>\<^sub>m\<^sub>a\<^sub>x"
    using I_mat_def assms(2) by fastforce
  show ?thesis 
    using I_mat_def assms(2) by fastforce
qed

(*################################################################################################*)

(* Call all the definitions that predefined with their constants and variables*)
definition "set_of_definitions \<omega> \<omega>\<^sub>r\<^sub>e\<^sub>f \<omega>' \<omega>'\<^sub>r\<^sub>e\<^sub>f u u\<^sub>d \<xi> \<xi>' \<xi>'' q q' q\<^sub>r q\<^sub>r' q\<^sub>e \<tau> \<tau>\<^sub>d 
                               \<eta> y \<zeta> C C\<^sub>h\<^sub>a\<^sub>t \<Delta>  A G \<Gamma> Z\<^sub>t Q P K\<^sub>q K\<^sub>\<omega> I I\<^sub>h\<^sub>a\<^sub>t  
= (
I_mat I \<and> I\<^sub>h\<^sub>a\<^sub>t_mat I\<^sub>h\<^sub>a\<^sub>t \<and> \<Gamma>_mat \<Gamma> \<omega> \<and> K\<^sub>q_mat K\<^sub>q \<and> K\<^sub>\<omega>_mat K\<^sub>\<omega> \<and> Z\<^sub>t_mat Z\<^sub>t q \<and> A_mat A \<and> 
G_mat G \<and> P_mat P \<and> Q_mat Q \<and> torq_fun \<tau> \<and> C_fun C \<Gamma> I \<omega> \<and> att_dyms \<omega> \<omega>' I C \<Gamma> \<tau> \<tau>\<^sub>d \<and>
quat_error q\<^sub>e q\<^sub>r q \<and> error_fun \<xi> q\<^sub>e \<and> dot_q\<^sub>r_fun q\<^sub>r' q\<^sub>e K\<^sub>q \<xi>  \<and> dot_error_fun \<xi>' q' q\<^sub>r' \<omega> \<omega>\<^sub>r\<^sub>e\<^sub>f Z\<^sub>t \<and>       
dot_ang_vel \<omega>\<^sub>r\<^sub>e\<^sub>f \<omega>'\<^sub>r\<^sub>e\<^sub>f \<and> y_eq y u I I\<^sub>h\<^sub>a\<^sub>t \<Delta> \<tau>\<^sub>d \<and> cont_u_def u \<omega>'\<^sub>r\<^sub>e\<^sub>f K\<^sub>\<omega> K\<^sub>q \<xi>' \<xi> \<and> zeta_def \<zeta> y \<and>
 u\<^sub>d_def u\<^sub>d G Q \<zeta> \<eta> \<and> C\<^sub>h\<^sub>a\<^sub>t_fun C\<^sub>h\<^sub>a\<^sub>t \<Gamma> I\<^sub>h\<^sub>a\<^sub>t \<omega> \<and> cont_law \<tau> I\<^sub>h\<^sub>a\<^sub>t u u\<^sub>d C\<^sub>h\<^sub>a\<^sub>t \<and> \<eta>_vec \<eta> \<xi> \<xi>' \<and>
 ddot_error_fun \<xi>'' \<xi>' \<omega>' \<omega>'\<^sub>r\<^sub>e\<^sub>f )"

lemma matrix_unity: 
  fixes I :: "real^3^3"
    and x :: "real^3" 
assumes "invertible I"
  shows "matrix_inv(I) *v (I *v x) = x" 
proof-
    have x1: "matrix_inv(I) *v (I *v x) = (matrix_inv(I) ** I) *v x " 
      by (simp add: matrix_vector_mul_assoc)
    have "I ** matrix_inv(I) = mat 1"  
      by (smt assms matrix_inv_def invertible_def matrix_matrix_mult_def someI2)   
    from this x1 have "(matrix_inv(I) ** I) *v x =  x" 
      using matrix_left_right_inverse matrix_vector_mul_lid by force
    thus ?thesis 
      using x1 by auto
qed

lemma matrix_diff_vect_distrib: "(A - B) *v x = A *v x - B *v (x :: 'a :: ring_1 ^ 'n)"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum_subtractf left_diff_distrib)

lemma matrix_add_vect_distrib: "(A + B) *v x = A *v x + B *v x"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum.distrib distrib_right)

lemma matrix_vector_right_distrib: "M *v (x + w) = M *v x + M *v w"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum.distrib distrib_left)

lemma matrix_vector_right_distrib_diff: "(M :: 'a :: ring_1 ^ 'nr ^ 'nc) *v (y - w) = M *v y - M *v w"
  unfolding matrix_vector_mult_def
  by vector (simp add: sum_subtractf right_diff_distrib)

(* Eq (26) *)
theorem Eq_26:
  assumes "assump3 \<tau>\<^sub>d" and "\<Delta> = C\<^sub>h\<^sub>a\<^sub>t - C" and "\<forall>t. t\<in>T"
      and "att_dyms \<omega> \<omega>' I C \<Gamma> \<tau> \<tau>\<^sub>d" and "cont_law \<tau> I\<^sub>h\<^sub>a\<^sub>t u u\<^sub>d C\<^sub>h\<^sub>a\<^sub>t" 
      and "I_mat I" and "I\<^sub>h\<^sub>a\<^sub>t_mat I\<^sub>h\<^sub>a\<^sub>t" and "y_eq y u I I\<^sub>h\<^sub>a\<^sub>t \<Delta> \<tau>\<^sub>d" 
    shows "\<omega>' = u + matrix_inv(I)*v u\<^sub>d - y " 
proof-
  have "\<tau> = I *v \<omega>' + C + \<tau>\<^sub>d"  
    using assms att_dyms_def by blast  
  then have "I *v \<omega>' + C + \<tau>\<^sub>d = I\<^sub>h\<^sub>a\<^sub>t *v u + u\<^sub>d + C\<^sub>h\<^sub>a\<^sub>t" 
    unfolding cont_law_def using assms cont_law_def by blast
  then have "I *v \<omega>' = I\<^sub>h\<^sub>a\<^sub>t *v u + u\<^sub>d + C\<^sub>h\<^sub>a\<^sub>t - C - \<tau>\<^sub>d" 
    by (metis (mono_tags, lifting) add_diff_cancel diff_add_eq)
  then have "\<omega>' = matrix_inv(I) *v (I\<^sub>h\<^sub>a\<^sub>t *v u + u\<^sub>d + \<Delta> - \<tau>\<^sub>d)" 
    using assms matrix_unity I_mat_def add_diff_eq by (metis (no_types, lifting))
  then have "\<omega>' = (matrix_inv(I) ** I\<^sub>h\<^sub>a\<^sub>t) *v u + matrix_inv(I) *v u\<^sub>d +  matrix_inv(I) *v (\<Delta> - \<tau>\<^sub>d)" 
    by (metis (no_types, lifting) diff_diff_eq2 diff_minus_eq_add matrix_vector_mul_assoc
        matrix_vector_right_distrib_diff minus_diff_eq)    
  then have "\<omega>' = u + ((matrix_inv(I) ** I\<^sub>h\<^sub>a\<^sub>t)- mat 1)*v u + matrix_inv(I) *v u\<^sub>d + matrix_inv(I) *v (\<Delta> - \<tau>\<^sub>d)"
    by (simp add: matrix_diff_vect_distrib add_diff_eq)
  then have x1:"\<omega>' = u - ((mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(I)*v (\<Delta>-\<tau>\<^sub>d)) + matrix_inv(I) *v u\<^sub>d"
    by (simp add: diff_add_eq matrix_diff_vect_distrib)
  have x2:"y = (mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(I)*v (\<Delta>-\<tau>\<^sub>d)"
    using assms y_eq_def by fast
  from x1 x2 show ?thesis 
    by simp
qed

(* Eq (29) *)
lemma Eq_29:
  assumes "\<forall>t. t\<in>T" 
     and "(set_of_definitions \<omega> \<omega>\<^sub>r\<^sub>e\<^sub>f \<omega>' \<omega>'\<^sub>r\<^sub>e\<^sub>f u u\<^sub>d \<xi> \<xi>' \<xi>'' q q' q\<^sub>r q\<^sub>r' q\<^sub>e \<tau> \<tau>\<^sub>d 
                               \<eta> y \<zeta> C C\<^sub>h\<^sub>a\<^sub>t \<Delta>  A G \<Gamma> Z\<^sub>t Q P K\<^sub>q K\<^sub>\<omega> I I\<^sub>h\<^sub>a\<^sub>t)"    
   shows "\<eta>' = A *v \<eta> + G *v (y - (matrix_inv(I) *v u\<^sub>d))"
proof -
  have "\<xi>'' = \<omega>'\<^sub>r\<^sub>e\<^sub>f - \<omega>'" 
    using assms ddot_error_fun_def set_of_definitions_def by metis
  thus ?thesis 
    by (smt G_mat_def assms(2) exhaust_3 set_of_definitions_def)
qed

(**************************************************************************************************)
section \<open>STABILITY ANALYSIS\<close>
(**************************************************************************************************)
(**************************************************************************************************)
text \<open>Lyapunov function\<close>
(**************************************************************************************************)
(*Lyapunov function definition*)
definition "Lyapunov V \<eta> = (\<forall>t\<in>T.  if (\<eta> :: (real,6) vec) \<noteq>0   
                     then (\<exists>a. V(\<eta>)= (a:: real) \<and> continuous_on D6_vec_set V  \<and> V(\<eta>)>0) else V(\<eta>) = 0)"
                                 
lemma test_lyp0:
  assumes "\<forall>t. t\<in>T" "\<eta>\<in>D6_vec_set"  "\<eta>=0" "Lyapunov V \<eta>"
    shows "V(\<eta>) = 0" using assms Lyapunov_def  by force

lemma test_lyp1:
  assumes "\<forall>t. t\<in>T" "\<eta>\<in>D6_vec_set"  "\<eta>\<noteq>0" "Lyapunov V \<eta>" 
    shows "V(\<eta>) >0" using assms Lyapunov_def    by metis

(* Eq (38) *)
lemma Lyp_fun:
  assumes "pos_def_symmetric_matrix Q" "\<forall>\<eta>. \<eta>\<noteq>0" 
  shows "\<exists>Q. (\<eta> \<bullet> (Q *v \<eta>))>0" 
    using assms pos_def_symmetric_matrix_def pos_def_6x6_matrix_def by blast

lemma vec_op:
  fixes A Q :: "real^6^6"
    and \<eta>:: "real^6"
  shows "(A *v \<eta>) \<bullet> (Q *v \<eta>) = \<eta> \<bullet> ((transpose(A) ** Q) *v \<eta>)"
    by (metis dot_matrix_product dot_matrix_vector_mul dot_rowvector_columnvector)

(* Eq (40), Lyapunov matrix A\<^sup>T*Q + Q*A = -P *)
lemma Lya_mat: 
  fixes A :: "((real, 6) vec, 6) vec" 
  assumes "pos_def_symmetric_matrix Q" and "pos_def_symmetric_matrix P" 
      and "A_mat A" and "P_mat P" and "Q_mat Q"
      and "det(A - (mat egn)) =0" and "egn<0" "\<forall>r. r \<noteq> 0"
    shows "\<exists>!Q. transpose (A) ** Q +  Q ** A = -P"  
      using assms pos_def_symmetric_matrix_def pos_def_6x6_matrix_def by blast

(**************************************************************************************************)
text \<open>Stability proof - Theorem 1\<close>
(**************************************************************************************************)
(* Eqs (39-41) *)
theorem Stb_Eq_39_41: 
 assumes "\<forall>\<eta>. \<eta>\<noteq>0"and"Lyapunov V \<eta>"and"V(\<eta>) = \<eta> \<bullet> (Q *v \<eta>)" 
     and "A_mat A"and"\<eta>' = A *v \<eta> + G *v (y - (matrix_inv(I) *v u\<^sub>d))"
     and "(\<forall>t\<in>T. ((\<lambda>t. V(\<eta>)) has_derivative (\<lambda>t. V'(\<eta>))) (at t within T))"
   shows "V'(\<eta>) = - (\<eta> \<bullet> (P *v \<eta>)) + 2 * (((\<eta> v* Q) v* G) \<bullet> (y - matrix_inv(I) *v u\<^sub>d))"
proof -
   have "V'(\<eta>) = \<eta>' \<bullet> (Q *v \<eta>) + \<eta> \<bullet> (Q *v \<eta>')" 
     using assms add_cancel_left_left rel_simps(93) by blast 
   then have "V'(\<eta>) = \<eta> \<bullet> ((transpose (A) ** Q + Q ** A)*v \<eta>) + 2*(((\<eta> v* Q) v* G) \<bullet> (y - matrix_inv(I) *v u\<^sub>d))"
     using assms Eq_29 vec_op  rel_simps(93) by simp
   then have "V'(\<eta>) = - (\<eta> \<bullet> (P *v \<eta>)) + 2 * (((\<eta> v* Q) v* G) \<bullet> (y - matrix_inv(I) *v u\<^sub>d))" 
     using assms by blast
   then show ?thesis 
     by blast
 qed

(* Eq (43) *)
theorem Eq_43:
  assumes "norm(transpose(G)*v(Q*v \<eta>)) \<ge> \<mu>"and"zeta_def \<zeta> y" "\<exists>\<eta>. \<eta>\<noteq>0" 
          "assump2 I I\<^sub>h\<^sub>a\<^sub>t"and"\<forall>t. t\<in>T" "(set_of_definitions \<omega> \<omega>\<^sub>r\<^sub>e\<^sub>f \<omega>' \<omega>'\<^sub>r\<^sub>e\<^sub>f u u\<^sub>d \<xi> \<xi>' \<xi>'' q q' q\<^sub>r q\<^sub>r' q\<^sub>e \<tau> \<tau>\<^sub>d 
                               \<eta> y \<zeta> C C\<^sub>h\<^sub>a\<^sub>t \<Delta>  A G \<Gamma> Z\<^sub>t Q P K\<^sub>q K\<^sub>\<omega> I I\<^sub>h\<^sub>a\<^sub>t)" 
    shows "(((\<eta> v* Q) v* G) \<bullet> (y - matrix_inv(I) *v u\<^sub>d)) \<le> norm (transpose (G) *v (Q*v \<eta>))* (norm(y) - (\<II>\<^sub>m\<^sub>i\<^sub>n * \<zeta>)) "
proof - 
  have x1:"((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) = (((\<eta> v* Q) v* G) \<bullet>  y) - (((\<eta> v* Q) v* G) \<bullet> (matrix_inv(I) *v u\<^sub>d)) "
    by (simp add: inner_diff_right)     
  then have x2:" norm((((\<eta> v* Q) v* G) \<bullet>  y) - (((\<eta> v* Q) v* G) \<bullet> (matrix_inv(I) *v u\<^sub>d))) \<le> 
              norm (((\<eta> v* Q) v* G) \<bullet>  y) + norm(((\<eta> v* Q) v* G) \<bullet> (matrix_inv(I) *v u\<^sub>d)) "
    using norm_triangle_ineq4 by blast
  have x3:"norm (((\<eta> v* Q) v* G) \<bullet>  y) \<le> norm ((\<eta> v* Q) v* G) * norm(y) " 
     by (simp add: Cauchy_Schwarz_ineq2)
   have x4:"norm(((\<eta> v* Q) v* G) \<bullet> (matrix_inv(I) *v u\<^sub>d)) \<le> norm((\<eta> v* Q) v* G) * norm(matrix_inv(I) *v u\<^sub>d)"
     by (simp add: Cauchy_Schwarz_ineq2)
   from x1 x2 x3 x4 have x5:"((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le> 
      norm((\<eta> v* Q) v* G) * norm(y) - ((\<eta> v* Q) v* G) \<bullet> (matrix_inv(I) *v u\<^sub>d)" 
     by fastforce
   have x6:"norm((\<eta> v* Q) v* G) = norm(transpose(G) *v (Q*v \<eta>)) "
    by (smt G_mat_def assms exhaust_3 set_of_definitions_def)
  from x5 x6 have "((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le> 
      norm(transpose(G) *v (Q*v \<eta>)) * norm(y) - (transpose(G) *v (Q*v \<eta>)) \<bullet> ((matrix_inv(I)) *v u\<^sub>d)"
    by (meson Eq_29 add_cancel_left_left assms rel_simps(93))
  then have "((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le> 
      norm(transpose(G) *v (Q *v \<eta>)) * norm(y) - (transpose(G) *v (Q*v \<eta>)) \<bullet> ( norm(matrix_inv(I)) *s u\<^sub>d)"
    by (meson Eq_29 add_cancel_left_left assms(5) assms(6) rel_simps(93))
  then have "((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le> 
      norm(transpose(G) *v (Q*v \<eta>)) * norm(y) - norm(matrix_inv(I)) *((transpose(G) *v (Q*v \<eta>)) \<bullet> u\<^sub>d)"
    by(simp add:  scalar_mult_eq_scaleR)  
  then have "((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le>
      norm(transpose(G) *v (Q *v \<eta>)) * norm(y) - \<II>\<^sub>m\<^sub>i\<^sub>n *((transpose(G) *v (Q*v \<eta>)) \<bullet> u\<^sub>d)"
    using  set_of_definitions_def assump2_def by (smt G_mat_def assms(6) exhaust_3)
  then have "((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le>
      norm(transpose(G) *v (Q*v \<eta>)) * norm(y) - \<II>\<^sub>m\<^sub>i\<^sub>n * norm(transpose(G) *v (Q*v \<eta>)) * norm(u\<^sub>d)"
    using  set_of_definitions_def assump2_def by (smt G_mat_def assms(6) exhaust_3)
  then have "((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le>
      norm(transpose(G) *v (Q*v \<eta>)) *(norm(y) - \<II>\<^sub>m\<^sub>i\<^sub>n *  norm(u\<^sub>d))"
    by (smt inner_diff_right inner_real_def mult.assoc mult.left_commute)
  then have "((\<eta> v* Q) v* G) \<bullet>  (y - matrix_inv(I) *v u\<^sub>d) \<le>
      norm(transpose(G) *v (Q*v \<eta>)) *(norm(y) - \<II>\<^sub>m\<^sub>i\<^sub>n * \<zeta>)"
    by (smt G_mat_def assms(6) exhaust_3 rel_simps(93) set_of_definitions_def)
  thus ?thesis 
    by blast
qed

(* Eq (45) *)
theorem Eq_45:
  assumes "(set_of_definitions \<omega> \<omega>\<^sub>r\<^sub>e\<^sub>f \<omega>' \<omega>'\<^sub>r\<^sub>e\<^sub>f u u\<^sub>d \<xi> \<xi>' \<xi>'' q q' q\<^sub>r q\<^sub>r' q\<^sub>e \<tau> \<tau>\<^sub>d 
                               \<eta> y \<zeta> C C\<^sub>h\<^sub>a\<^sub>t \<Delta>  A G \<Gamma> Z\<^sub>t Q P K\<^sub>q K\<^sub>\<omega> I I\<^sub>h\<^sub>a\<^sub>t)" 
     and "assump1 \<omega>'\<^sub>r\<^sub>e\<^sub>f" and "assump2 I I\<^sub>h\<^sub>a\<^sub>t" and "assump3 \<tau>\<^sub>d" "\<forall>t. t\<in>T"
   shows "norm (y) \<le> (\<delta> * (\<alpha> + (norm(K\<^sub>\<omega>)*norm(\<xi>'))+ (norm(K\<^sub>q)*norm(\<xi>))) + (\<II>\<^sub>m\<^sub>a\<^sub>x*(\<beta> + \<gamma>)))" 
proof-
  have "y = (mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(I)*v (\<Delta>-\<tau>\<^sub>d)" 
    using assms y_eq_def set_of_definitions_def by fast
  then have "norm(y) \<le> norm((mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t))*v u - matrix_inv(I)*v (\<Delta>-\<tau>\<^sub>d))"
    by fastforce
  then have "norm(y) \<le> norm((mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) *v u) + norm((matrix_inv(I)) *v (\<Delta>-\<tau>\<^sub>d))"
    using norm_triangle_ineq4 order_trans by blast
  then have "norm(y) \<le> (norm(mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) * norm(u)) + (norm(matrix_inv(I)) * (norm(\<Delta>) + norm(\<tau>\<^sub>d)))"
     by (smt G_mat_def assms(1) exhaust_3 set_of_definitions_def)
  then have "norm(y) \<le> norm(mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) * norm(\<omega>'\<^sub>r\<^sub>e\<^sub>f + K\<^sub>\<omega> *v \<xi>' + K\<^sub>q *v \<xi>) 
                     + norm (matrix_inv(I))* (norm(\<Delta>)+ norm(\<tau>\<^sub>d))"  
    using assms cont_u_def_def set_of_definitions_def by metis
  then have "norm(y) \<le> norm(mat 1-(matrix_inv(I)**I\<^sub>h\<^sub>a\<^sub>t)) * (norm(\<omega>'\<^sub>r\<^sub>e\<^sub>f) + (norm(K\<^sub>\<omega>) * norm(\<xi>')) + (norm(K\<^sub>q) * norm(\<xi>)))
                     + norm (matrix_inv(I))* (norm(\<Delta>)+ norm(\<tau>\<^sub>d))"
    using assms norm_add_rule_thm G_mat_def exhaust_3 set_of_definitions_def by smt  
  then have "norm(y) \<le> \<delta> * (\<alpha> + (norm(K\<^sub>\<omega>) * norm(\<xi>')) + (norm(K\<^sub>q) * norm(\<xi>)))
                     + \<II>\<^sub>m\<^sub>a\<^sub>x * (\<beta>+\<gamma>)"   
    by (meson assms assump1_def assump2_def assump3_def mult_nonneg_nonneg norm_ge_zero mult_right_mono mult_mono 
          mult_nonneg_nonneg mult_right_mono norm_ge_zero less_irrefl Eq_29 add_cancel_left_right rel_simps(93))
  thus ?thesis 
    by blast
qed

(* Eq (46) *)
theorem Eq_46:
  assumes "\<forall>t. t\<in>T""zeta_def \<zeta> y"
      and "norm(y) \<le> \<delta> * (\<alpha> + (norm(K\<^sub>\<omega>)*norm(\<xi>'))+ (norm(K\<^sub>q)*norm(\<xi>))) + (\<II>\<^sub>m\<^sub>a\<^sub>x*(\<beta>+\<gamma>))" (*from Eq_45*)
    shows "\<exists>\<zeta>. \<zeta> \<ge> (\<delta>/\<II>\<^sub>m\<^sub>i\<^sub>n) * (\<alpha> + (norm(K\<^sub>\<omega>) * norm(\<xi>')) + (norm(K\<^sub>q) * norm(\<xi>))) + (\<II>\<^sub>m\<^sub>a\<^sub>x/\<II>\<^sub>m\<^sub>i\<^sub>n)*(\<beta> + \<gamma>)"
proof-
  fix x y:: "real^3"
  have x1:"\<II>\<^sub>m\<^sub>a\<^sub>x>0 \<and> \<II>\<^sub>m\<^sub>i\<^sub>n>0 \<and> \<beta>>0 \<and> \<gamma>>0 \<and> \<delta>>0 \<and> \<alpha>>0 \<and> norm x\<ge>0" 
    using \<II>\<^sub>m\<^sub>a\<^sub>x_def \<II>\<^sub>m\<^sub>i\<^sub>n_def \<beta>_def \<gamma>_def \<delta>_def \<alpha>_def by force
  have x2:"y>0 \<Longrightarrow> 0+y>0"  by simp
  from x1 x2 have x3:"(\<delta> * (\<alpha> + (norm(K\<^sub>\<omega>)*norm(\<xi>'))+ (norm(K\<^sub>q)*norm(\<xi>))) + (\<II>\<^sub>m\<^sub>a\<^sub>x*(\<beta>+\<gamma>))) > 0" 
    by (smt distrib_left mult.commute mult_nonneg_nonneg norm_ge_zero real_mult_le_cancel_iff1)
  then have "\<exists>\<zeta>. \<zeta> \<ge> (\<delta> * (\<alpha> + (norm(K\<^sub>\<omega>)*norm(\<xi>'))+ (norm(K\<^sub>q)*norm(\<xi>))) + (\<II>\<^sub>m\<^sub>a\<^sub>x*(\<beta>+\<gamma>)))/\<II>\<^sub>m\<^sub>i\<^sub>n" 
    using assms \<II>\<^sub>m\<^sub>i\<^sub>n_def zeta_def_def  divide_pos_pos divide_strict_right_mono by blast
  then have "\<exists>\<zeta>. \<zeta> \<ge> (\<delta>/\<II>\<^sub>m\<^sub>i\<^sub>n) * (\<alpha> + (norm(K\<^sub>\<omega>)*norm(\<xi>'))+ (norm(K\<^sub>q)*norm(\<xi>))) + (\<II>\<^sub>m\<^sub>a\<^sub>x*(\<beta>+\<gamma>))/\<II>\<^sub>m\<^sub>i\<^sub>n"
    by argo
  thus ?thesis 
    by auto
qed

(* Eq (47-49) *)
theorem Stb_Eq_47_49:
assumes "(set_of_definitions \<omega> \<omega>\<^sub>r\<^sub>e\<^sub>f \<omega>' \<omega>'\<^sub>r\<^sub>e\<^sub>f u u\<^sub>d \<xi> \<xi>' \<xi>'' q q' q\<^sub>r q\<^sub>r' q\<^sub>e \<tau> \<tau>\<^sub>d 
                               \<eta> y \<zeta> C C\<^sub>h\<^sub>a\<^sub>t \<Delta>  A G \<Gamma> Z\<^sub>t Q P K\<^sub>q K\<^sub>\<omega> I I\<^sub>h\<^sub>a\<^sub>t)" 
    and "assump1 \<omega>'\<^sub>r\<^sub>e\<^sub>f" and "assump2 I I\<^sub>h\<^sub>a\<^sub>t"
    and "assump3 \<tau>\<^sub>d" and "\<Delta> = C\<^sub>h\<^sub>a\<^sub>t - C" "\<forall>t. t\<in>T" and "\<forall>\<eta>. \<eta>\<noteq>0"
    and "Lyapunov V \<eta>" and "V(\<eta>) = \<eta> \<bullet> (Q *v \<eta>)"
    and "(\<forall>t\<in>T. ((\<lambda>t. V(\<eta>)) has_derivative (\<lambda>t. V'(\<eta>))) (at t within T))"
    and "\<omega>' = u - y + matrix_inv(I)*v u\<^sub>d" (* from Eq_29 *)
    and "\<eta>' = A *v \<eta> + G *v (y - (matrix_inv(I) *v u\<^sub>d))" (* from Eq_29 *)
    and "V'(\<eta>) = - (\<eta> \<bullet> (P *v \<eta>)) + 2 * (\<eta> \<bullet> (Q *v (G *v (y - matrix_inv (I) *v u\<^sub>d))))"
  shows "norm (transpose (G) *v (Q*v \<eta>)) \<ge> \<mu> \<Longrightarrow> V'(\<eta>) < 0" 
    and "norm (transpose (G) *v (Q*v \<eta>)) < \<mu> \<Longrightarrow> V'(\<eta>) < 0"
    and "((\<lambda>t. norm(\<eta>)) \<longlongrightarrow> 0) (at t within T)"
proof- 
   show "norm (transpose (G) *v (Q*v \<eta>)) \<ge> \<mu> \<Longrightarrow> V'(\<eta>) < 0"
    using assms Eq_29 rel_simps(93) by metis
  then show "norm (transpose (G) *v (Q*v \<eta>)) < \<mu> \<Longrightarrow> V'(\<eta>) < 0"
    using assms Eq_29 rel_simps(93) by metis
  show "((\<lambda>t. norm(\<eta>)) \<longlongrightarrow> 0) (at t within T)" 
    using assms by auto
qed  

end