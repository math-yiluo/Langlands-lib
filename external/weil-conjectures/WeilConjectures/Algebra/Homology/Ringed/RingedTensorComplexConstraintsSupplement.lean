/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Pure-section formulas for the tensor constraints of module-sheaf complexes

Source: Stacks Project, Tag 0FPQ, and the sign rules of More on Algebra.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
open Functor.LaxMonoidal Functor.OplaxMonoidal
namespace CategoryTheory.RingedDerivedNative

section Generic
variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
  [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : A, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

omit [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem leftUnitor_summand (P : CochainComplex A ℤ) (n : ℤ) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) (𝟙_ A)).inv ▷ P.X n ≫
      HomologicalComplex.ιTensorObj (𝟙_ _) P 0 n n (zero_add n) ≫
        (λ_ P).hom.f n = (λ_ (P.X n)).hom := by
  apply (cancel_epi (λ_ (P.X n)).inv).1
  calc
    _ = (λ_ P).inv.f n ≫ (λ_ P).hom.f n := by
      rw [show (λ_ P).inv.f n = _ from HomologicalComplex.leftUnitor'_inv P n]
      simp only [Category.assoc]
      rfl
    _ = 𝟙 _ := congrArg (fun f ↦ f.f n) (λ_ P).inv_hom_id
    _ = _ := (λ_ (P.X n)).inv_hom_id.symm

omit [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem rightUnitor_summand (P : CochainComplex A ℤ) (n : ℤ) :
    P.X n ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) (𝟙_ A)).inv ≫
      HomologicalComplex.ιTensorObj P (𝟙_ _) n 0 n (add_zero n) ≫
        (ρ_ P).hom.f n = (ρ_ (P.X n)).hom := by
  apply (cancel_epi (ρ_ (P.X n)).inv).1
  calc
    _ = (ρ_ P).inv.f n ≫ (ρ_ P).hom.f n := by
      rw [show (ρ_ P).inv.f n = _ from HomologicalComplex.rightUnitor'_inv P n]
      simp only [Category.assoc]
      rfl
    _ = 𝟙 _ := congrArg (fun f ↦ f.f n) (ρ_ P).inv_hom_id
    _ = _ := (ρ_ (P.X n)).inv_hom_id.symm

omit [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z] in
private theorem associator_summand (P Q N : CochainComplex A ℤ)
    (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n) :
    (HomologicalComplex.ιTensorObj P Q p q pq hpq ▷ N.X r) ≫
        HomologicalComplex.ιTensorObj (P ⊗ Q) N pq r n hn ≫ (α_ P Q N).hom.f n =
      (α_ (P.X p) (Q.X q) (N.X r)).hom ≫
        (P.X p ◁ HomologicalComplex.ιTensorObj Q N q r qr hqr) ≫
          HomologicalComplex.ιTensorObj P (Q ⊗ N) p qr n hn' := by
  have ha := CochainComplex.Monoidal.ι₁₂_associator_hom P Q N p q r n (by omega)
  rw [CochainComplex.Monoidal.ι₁₂_eq P Q N p q r pq n hpq hn,
    CochainComplex.Monoidal.ι₂₃_eq P Q N p q r qr n hqr hn'] at ha
  simpa only [Category.assoc] using ha
end Generic

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev ring :=
  (sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R

private abbrev forgetModules :=
  SheafOfModules.forget (ring.{c, v, u} J R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ring.{c, v, u} J R).obj)

private abbrev tensorAdj :=
  PresheafOfModules.sheafificationAdjunction.{max c v u} (𝟙 (ring.{c, v, u} J R).obj)

@[reducible] private noncomputable def forgetLax : (forgetModules.{c, v, u} J R).LaxMonoidal :=
  (tensorAdj.{c, v, u} J R).rightAdjointLaxMonoidal

attribute [local instance] forgetLax

private theorem forget_ε : ε (forgetModules.{c, v, u} J R) = 𝟙 _ := by
  let adj := tensorAdj.{c, v, u} J R
  have h : η (PresheafOfModules.sheafification.{max c v u}
      (𝟙 (ring.{c, v, u} J R).obj)) =
      adj.counit.app (𝟙_ (Modules.{c, v, u} J R)) := rfl
  change adj.homEquiv _ _ (η _) = _
  rw [h, Adjunction.homEquiv_unit]
  exact adj.right_triangle_components (𝟙_ (Modules.{c, v, u} J R))

private abbrev pureTensor (M N : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :=
  CochainPullback.moduleTmul (R := R) M N U x y

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private theorem pureTensor_map {M N M' N' : Modules.{c, v, u} J R}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U (pureTensor.{c, v, u} J R M N U x y) =
      pureTensor.{c, v, u} J R M' N' U (f.val.app U x) (g.val.app U y) :=
  CochainPullback.moduleTmul_map f g U x y

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private theorem pureTensor_associator (M N T : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (z : T.val.obj U) :
    (α_ M N T).hom.val.app U
        (pureTensor.{c, v, u} J R (M ⊗ N) T U
          (pureTensor.{c, v, u} J R M N U x y) z) =
      pureTensor.{c, v, u} J R M (N ⊗ T) U x
        (pureTensor.{c, v, u} J R N T U y z) :=
  CochainPullback.moduleTmul_associator M N T U x y z

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private theorem pureTensor_braiding (M N : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (β_ M N).hom.val.app U (pureTensor.{c, v, u} J R M N U x y) =
      pureTensor.{c, v, u} J R N M U y x :=
  CochainPullback.moduleTmul_braiding M N U x y

private theorem pureTensor_mu (M N : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    pureTensor.{c, v, u} J R M N U x y =
      (μ (forgetModules.{c, v, u} J R) M N).app U (x ⊗ₜ[R.obj.obj U] y) := by rfl

private theorem pureTensor_leftUnitor (M : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) :
    (λ_ M).hom.val.app U (pureTensor.{c, v, u} J R (𝟙_ _) M U a x) = a • x := by
  rw [pureTensor_mu]
  have h := Functor.LaxMonoidal.left_unitality (forgetModules.{c, v, u} J R) M
  rw [forget_ε, id_whiskerRight, Category.id_comp] at h
  exact congrArg (fun k ↦ k.app U (a ⊗ₜ[R.obj.obj U] x)) h.symm

private theorem pureTensor_rightUnitor (M : Modules.{c, v, u} J R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) :
    (ρ_ M).hom.val.app U (pureTensor.{c, v, u} J R M (𝟙_ _) U x a) = a • x := by
  rw [pureTensor_mu]
  have h := Functor.LaxMonoidal.right_unitality (forgetModules.{c, v, u} J R) M
  rw [forget_ε, MonoidalCategory.whiskerLeft_id, Category.id_comp] at h
  exact congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] a)) h.symm

end

/-- The symmetry equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def symmetryPure : Prop :=
  ∀ (P Q : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (p q n : ℤ) (h : p + q = n) (h' : q + p = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((β_ P Q).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R P Q p q n h U x y) =
    (p * q).negOnePow • coefficientTensorGenerator.{u, c, v} J R Q P q p n h' U y x

/-- The associator equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def associatorPure : Prop :=
  ∀ (P Q N : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
    ((α_ P Q N).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R (P ⊗ Q) N pq r n hn U
        (coefficientTensorGenerator.{u, c, v} J R P Q p q pq hpq U x y) z) =
    coefficientTensorGenerator.{u, c, v} J R P (Q ⊗ N) p qr n hn' U x
      (coefficientTensorGenerator.{u, c, v} J R Q N q r qr hqr U y z)

/-- The leftUnitor equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def leftUnitorPure : Prop :=
  ∀ (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (n : ℤ) (h : 0 + n = n) (U : Cᵒᵖ) (a : R.obj.obj U) (x : (P.X n).val.obj U),
    ((λ_ P).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R (𝟙_ _) P 0 n n h U
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (𝟙_ (Modules.{c, v, u} J R))).inv.val.app U) a) x) = a • x

/-- The rightUnitor equation on homogeneous pure sections.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
def rightUnitorPure : Prop :=
  ∀ (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (n : ℤ) (h : n + 0 = n) (U : Cᵒᵖ) (a : R.obj.obj U) (x : (P.X n).val.obj U),
    ((ρ_ P).hom.f n).val.app U
      (coefficientTensorGenerator.{u, c, v} J R P (𝟙_ _) n 0 n h U x
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (𝟙_ (Modules.{c, v, u} J R))).inv.val.app U) a)) = a • x

/-- Pure-section descriptions of the constructed complex constraints.
Source: Stacks 0FPQ (blueprint: lem-sf-ringed-tensor-complex-constraints). -/
structure ComplexConstraints : Prop where
  symmetry : symmetryPure.{c, v, u} J R
  associator : associatorPure.{c, v, u} J R
  leftUnitor : leftUnitorPure.{c, v, u} J R
  rightUnitor : rightUnitorPure.{c, v, u} J R

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem generator_eq
    (P Q : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    coefficientTensorGenerator.{u, c, v} J R P Q p q n h U x y =
      (HomologicalComplex.ιTensorObj P Q p q n h).val.app U
        (pureTensor.{c, v, u} J R (P.X p) (Q.X q) U x y) := by rfl

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private theorem zsmul_apply {M N : Modules.{c, v, u} J R} (f : M ⟶ N)
    (a : ℤ) (U : Cᵒᵖ) (x : M.val.obj U) :
    (a • f).val.app U x = a • f.val.app U x := by
  have h := (SheafOfModules.forget (ring.{c, v, u} J R)).map_zsmul (f := f) (r := a)
  change (a • f).val = a • f.val at h
  rw [h, PresheafOfModules.zsmul_app]
  rfl

private theorem symmetry_formula : symmetryPure.{c, v, u} J R := by
  intro P Q p q n h h' U x y
  simp only [generator_eq]
  have hb := CochainComplex.Monoidal.ι_braiding_hom (K := P) (L := Q) p q n h
  have he := congrArg (fun f ↦ f.val.app U
    (pureTensor.{c, v, u} J R (P.X p) (Q.X q) U x y)) hb
  rw [zsmul_apply] at he
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at he
  have hs := pureTensor_braiding.{c, v, u} J R (P.X p) (Q.X q) U x y
  refine he.trans ?_
  exact congrArg (fun t : ((Q ⊗ P).X n).val.obj U ↦ ((p * q).negOnePow : ℤ) • t)
    (congrArg ((HomologicalComplex.ιTensorObj Q P q p n h').val.app U) hs)

private theorem associator_formula : associatorPure.{c, v, u} J R := by
  intro P Q N p q r pq qr n hpq hqr hn hn' U x y z
  simp only [generator_eq]
  have ha := associator_summand P Q N p q r pq qr n hpq hqr hn hn'
  have he := congrArg (fun f ↦ f.val.app U
    (pureTensor.{c, v, u} J R (P.X p ⊗ Q.X q) (N.X r) U
      (pureTensor.{c, v, u} J R (P.X p) (Q.X q) U x y) z)) ha
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, ← id_tensorHom, pureTensor_map, pureTensor_associator] at he
  exact he

private theorem leftUnitor_formula : leftUnitorPure.{c, v, u} J R := by
  intro P n h U a x
  simp only [generator_eq]
  have hs := leftUnitor_summand P n
  have he := congrArg (fun f ↦ f.val.app U
    (pureTensor.{c, v, u} J R (𝟙_ _) (P.X n) U a x)) hs
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, pureTensor_map] at he
  have hu := pureTensor_leftUnitor.{c, v, u} J R (P.X n) U a x
  exact he.trans hu

private theorem rightUnitor_formula : rightUnitorPure.{c, v, u} J R := by
  intro P n h U a x
  simp only [generator_eq]
  have hs := rightUnitor_summand P n
  have he := congrArg (fun f ↦ f.val.app U
    (pureTensor.{c, v, u} J R (P.X n) (𝟙_ _) U x a)) hs
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    ← id_tensorHom, pureTensor_map] at he
  have hu := pureTensor_rightUnitor.{c, v, u} J R (P.X n) U a x
  exact he.trans hu

end

/-- The native complex constraints have the usual signed pure-section formulas.
Source: Stacks Project, Tag 0FPQ, and More on Algebra, sign rules
(blueprint: lem-sf-ringed-tensor-complex-constraints).

Proof: write a generator as the sheafification unit on a presheaf pure tensor,
followed by the inverse tensor-sheafification comparison and the inclusion of its
bidegree summand. The sheafification functor is braided monoidal. Its tensorator's
naturality and the counit's naturality identify the sheaf symmetry on this generator
with the presheaf swap. The complex braiding on the (p,q) summand is the sheaf swap
multiplied by (-1)^(pq); apply the component formula for the Koszul braiding.
For the associator, use its formula on the (p,q,r) summand of the iterated direct sum.
Naturality of the sheafification unit in each tensor factor and the associativity
identity of its monoidal tensorator reduce both sides to the image of
(x tensor y) tensor z under the ordinary module associator, which is
x tensor (y tensor z). There is no interchange of homogeneous factors and no sign.
For the unitors, all summands except degree zero in the unit complex vanish.
The surviving summand is the coefficient ring tensor P^n, respectively P^n tensor
the coefficient ring. The single-complex degree-zero comparison identifies its
specified section with a. The unitality identities of the sheafification tensorator
reduce the maps to the ordinary module unitors, both sending the pure tensor to a*x.
These equalities hold on every object U and every indicated section, independently
of K-flatness, boundedness, the characteristic, and whether the coefficient ring is zero. -/
theorem complexConstraints : ComplexConstraints.{c, v, u} J R := by
  exact ⟨symmetry_formula.{c, v, u} J R, associator_formula.{c, v, u} J R,
    leftUnitor_formula.{c, v, u} J R, rightUnitor_formula.{c, v, u} J R⟩

end CategoryTheory.RingedDerivedNative
