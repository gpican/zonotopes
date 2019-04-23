#include <stdio.h>
#include <stdlib.h>
#define max(a,b) \
  ({ __typeof__ (a) _a = (a); \
      __typeof__ (b) _b = (b); \
    _a > _b ? _a : _b; })

int nbApprox = 0;

struct abstract_var{
  float tab[10];
  int cpt;
  float born_inf;
  float born_sup;
};

struct ineq{
// 1: fst_param => snd_param   0: fst_param < snd_param
  int res_eq;
  int fst_param;
  int snd_param;
};



typedef struct abstract_var abstractVar;

float born_inf_ab(abstractVar *ab){
  float res = ab->tab[0];
  for (size_t i = 1; i <= ab->cpt; i++) {
    if (ab->tab[i] <= 0) {
      res += ab->tab[i];
    } else {
      res -= ab->tab[i];
    }
  }
  return res;
}

float born_sup_ab(abstractVar *ab){
  float res = ab->tab[0];
  for (size_t i = 1; i <= ab->cpt; i++) {
    if (ab->tab[i] <= 0) {
      res -= ab->tab[i];
    } else {
      res += ab->tab[i];
    }
  }
  return res;
}

abstractVar* Object_new(int cpt, float value, int new_approx) {
  abstractVar* p = malloc(sizeof(abstractVar));
  p->cpt = cpt;
  p->tab[0] = value;
  if (new_approx){nbApprox +=1;}
  p->tab[nbApprox] = 1;
  p->born_inf = born_inf_ab(p);
  p->born_sup = born_sup_ab(p);
  return p;
}

abstractVar* abstractVar_new(int n,float values[1 + n]) {
  abstractVar* p = malloc(sizeof(abstractVar));
  p->cpt = n;
  for (size_t i = 0; i <= n; i++) {
    p->tab[i] = values[i];
    if (i > nbApprox && values[i] != 0 ) {
      nbApprox = i;
    }
  }
  p->born_inf = born_inf_ab(p);
  p->born_sup = born_sup_ab(p);
  return p;
}

void add_Abstraction(abstractVar *ab) {
  nbApprox +=1;
  float delta = ab->born_sup/(ab->born_sup - ab->born_inf);
  float mu = -(ab->born_sup * ab->born_inf)/(2*(ab->born_sup - ab->born_inf));
  for (size_t i = 0; i <= nbApprox; i++) {
    ab->tab[i] = delta * ab->tab[i];
  }
  ab->tab[0] += mu;
  ab->tab[nbApprox] = mu;
  ab->cpt = nbApprox;
  ab->born_inf = born_inf_ab(ab);
  ab->born_sup = born_sup_ab(ab);

}

abstractVar* addition_abstractVar(abstractVar *ab1,abstractVar *ab2){
  int maxCpt = max(ab1->cpt,ab2->cpt);
  abstractVar* res = Object_new(maxCpt,0,0);
  for (size_t i = 0; i <= maxCpt; i++) {
      res->tab[i] = ab1->tab[i] + ab2->tab[i];
  }
  res->born_inf = born_inf_ab(res);
  res->born_sup = born_sup_ab(res);
  return res;
}

abstractVar* soustraction_abstractVar(abstractVar *ab1,abstractVar *ab2){
  int maxCpt = max(ab1->cpt,ab2->cpt);
  abstractVar* res = Object_new(maxCpt,0,0);
  for (size_t i = 0; i <= maxCpt; i++) {
      res->tab[i] = ab1->tab[i] - ab2->tab[i];
  }
  res->born_inf = born_inf_ab(res);
  res->born_sup = born_sup_ab(res);
  return res;
}

abstractVar* multiplication_abstractVar(abstractVar *ab1,abstractVar *ab2){
  int maxCpt = max(ab1->cpt,ab2->cpt);
  abstractVar* res = Object_new(maxCpt,0,1);


//calcul du coefficient de x0
  res->tab[0] = ab1->tab[0] * ab2->tab[0];
  float prodxiyi = 0.0;
  for (size_t i = 1; i <= maxCpt; i++) {
    prodxiyi += ab1->tab[i] * ab2->tab[i];
  }
  //calcul du coefficient des xi
  res->tab[0] += prodxiyi * 0.5;
  for (size_t i = 1; i <= maxCpt; i++) {
     res->tab[i] = ab1->tab[i] * ab2->tab[0] + ab2->tab[i] * ab1->tab[0];
  }
//calcul des coefficient de la nouvelle incertitude
float temp = 0;
for (int i = 1; i < maxCpt; i++){
  for (int j = i+1; j <= maxCpt; j++) {
    temp += ab1->tab[i] * ab2->tab[j] + ab2->tab[i] * ab1->tab[j];
  }
}
  res->tab[nbApprox] = -(temp + 0.5 * prodxiyi);
  res->cpt++;
  res->born_inf = born_inf_ab(res);
  res->born_sup = born_sup_ab(res);
  return res;
}

abstractVar* inversion_abstractVar(abstractVar *ab){
  abstractVar* res = Object_new(res->cpt,0,0);
  for (size_t i = 0; i <= res->cpt ; i++) {
      res->tab[i] = -1.0 * ab->tab[i];
  }
  res->born_inf = born_inf_ab(res);
  res->born_sup = born_sup_ab(res);
  return res;
}

void print_ab_var(abstractVar *ab){
  if (ab->tab[0] != 0.0) {
    printf("%.3f", ab->tab[0]);
  }
  for (int i = 1; i <= 9; i++) {
    if (ab->tab[i] > 0){
      printf(" +%.3f e%d",ab->tab[i],i );
    } else if (ab->tab[i] < 0) {
      printf(" %.3f e%d",ab->tab[i],i );
    }
  }
  printf("\nborne inf %f\n",ab->born_inf);
  printf("borne supp %f\n",ab->born_sup);
  printf("\n");
}

abstractVar* copie_abstractVar(abstractVar *ab){
  abstractVar* res = Object_new(ab->cpt,ab->tab[0],0);
  for (size_t i = 1; i <= ab->cpt; i++) {
    res->tab[i] = ab->tab[i];
  }
  res->born_inf = ab->born_inf;
  res->born_sup = ab->born_sup;
  return res;
}

void add_cst(abstractVar *ab,float c){
ab->tab[0] = ab->tab[0] + c;
ab->born_inf = born_inf_ab(ab);
ab->born_sup = born_sup_ab(ab);
}



int main(){
/*  abstractVar* a = Object_new(1,-1.0,1);
  abstractVar* b = Object_new(2,2,1);
  abstractVar* x = addition_abstractVar(a,b);
  abstractVar* y = inversion_abstractVar(a);
  abstractVar* z = multiplication_abstractVar(x,y);
  print_ab_var(z);*/
  //printf("z:   lb %f    ub %f\n",z->born_inf,z->born_sup);
  float arr1[2] = {0.5,0.5};
  float arr2[3] = {0.5,0,0.5};

  abstractVar*x1 = abstractVar_new(1,arr1);
  abstractVar*x2 = abstractVar_new(2,arr2);
  abstractVar*x3 = addition_abstractVar(x1,x2);
  abstractVar*x4 = soustraction_abstractVar(x1,x2);
  abstractVar*x5 = copie_abstractVar(x3);
  abstractVar*x6 = copie_abstractVar(x4);
  add_Abstraction(x6);
  abstractVar*x7 = soustraction_abstractVar(x5,x6);
  add_cst(x7,1);
  abstractVar*x8 = copie_abstractVar(x7);
  add_cst(x8,-2);
  abstractVar*x9 = copie_abstractVar(x7);
  abstractVar*x10 = copie_abstractVar(x8);
  add_Abstraction(x10);


  printf("x6:    ");
  print_ab_var(x6);
  printf("x7:    ");
  print_ab_var(x7);
  printf("x8:    ");
  print_ab_var(x8);
  printf("x9:    ");
  print_ab_var(x9);
  printf("x10:    ");
  print_ab_var(x10);
  return 0;
}
