/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupRealizationComplexData

/-! # Cochain obligations for resolution pairings

Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  globalPullbackMatesColimits cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

set_option linter.unusedSectionVars false in
private theorem tensor_hom_ext {M N P : X.Modules} {a b : M ⊗ N ⟶ P}
    (h : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) P).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h U.unop s t

set_option linter.unusedSectionVars false in
private theorem tensor_d (K L : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (p q : ℤ) :
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
      (HomologicalComplex.tensorObj K L).d (p + q) (p + q + 1) =
      K.d p (p + 1) ▷ L.X q ≫
        HomologicalComplex.ιTensorObj K L (p + 1) q (p + q + 1) (by omega) +
      p.negOnePow • (K.X p ◁ L.d q (q + 1) ≫
        HomologicalComplex.ιTensorObj K L p (q + 1) (p + q + 1) (by omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
      (show p + 1 + q = p + q + 1 by omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
      (show p + (q + 1) = p + q + 1 by omega)]
  simp

set_option linter.unusedSectionVars false in
private theorem app_zsmul_apply {A B : X.Modules}
    (n : ℤ) (f : A ⟶ B) (V : X.Opens) (z : Γ(A, V)) :
    (n • f).app V z = n • f.app V z := by
  let e : (A ⟶ B) →+ (Γ(A, V) →+ Γ(B, V)) :=
    { toFun := fun f ↦ (f.app V).hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact congrArg (fun f : Γ(A, V) →+ Γ(B, V) ↦ f z) (e.map_zsmul n f)

set_option linter.unusedSectionVars false in
private theorem app_val_apply {A B : X.Modules}
    (f : A ⟶ B) (V : X.Opens) (z : Γ(A, V)) :
    f.app V z = f.val.app (op V) z := rfl

set_option linter.unusedSectionVars false in
private theorem val_id_apply (A : X.Modules) (V : X.Opens) (z : Γ(A, V)) :
    (𝟙 A : A ⟶ A).val.app (op V) z = z := rfl

set_option linter.unusedSectionVars false in
private theorem extend_d_inv (K : CochainComplex X.Modules ℕ) (p : ℕ)
    (V : X.Opens) (a : Γ(K.X p, V)) :
    ((K.extend ComplexShape.embeddingUpNat).d (p : ℤ) (p + 1)).app V
      ((K.extendXIso ComplexShape.embeddingUpNat rfl).inv.app V a) =
      (K.extendXIso ComplexShape.embeddingUpNat (i := p + 1) (by simp)).inv.app V
        ((K.d p (p + 1)).app V a) := by
  have h : (K.extendXIso ComplexShape.embeddingUpNat rfl).inv ≫
      (K.extend ComplexShape.embeddingUpNat).d (p : ℤ) (p + 1) =
      K.d p (p + 1) ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i := p + 1) (by simp)).inv := by
    erw [K.extend_d_eq ComplexShape.embeddingUpNat (i := p) (j := p + 1)
      (i' := (p : ℤ)) (j' := (p : ℤ) + 1) rfl (by simp)]
    simp
  exact congrArg (fun f ↦ f.app V a) h

set_option linter.unusedSectionVars false in
private theorem whiskerRight_val {M M' N :
    SheafOfModules.{u} (moduleRings X.toRingedSpace)} (f : M ⟶ M')
    (V : X.Opens) (s : Γ(M, V)) (t : Γ(N, V)) :
    (f ▷ N).val.app (op V) (tmulSection s t) =
      tmulSection (f.val.app (op V) s) t := by
  exact whiskerRight_app_tmulSection (X := X) f s t

set_option linter.unusedSectionVars false in
private theorem whiskerLeft_val {M N N' :
    SheafOfModules.{u} (moduleRings X.toRingedSpace)} (g : N ⟶ N')
    (V : X.Opens) (s : Γ(M, V)) (t : Γ(N, V)) :
    (M ◁ g).val.app (op V) (tmulSection s t) =
      tmulSection s (g.val.app (op V) t) := by
  exact whiskerLeft_app_tmulSection (X := X) g s t

set_option backward.isDefEq.respectTransparency.types false in
-- Tensor sheaf instances and the three transported component formulas need extra elaboration.
/-- The assembled component maps satisfy the signed chain equation by Leibniz. Source: Stacks
Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-chain-equation).
Proof: equality of maps out of a total term can be tested on its coproduct inclusions.
For a nonnegative bidegree, equality out of the tensor sheaf is tested after the
sheafification unit, then on elementary tensors of sections on every open. The assumed
section formula computes l on these tensors. The total tensor differential is the sum
of the left differential and (-1)^p times the right differential; D.leibniz identifies
these with the target differential of D.pair. The extension isomorphisms identify all
nonnegative differentials with the original ones. A negative factor makes its summand
zero, so its equation is automatic. Thus the coproduct equations prove the chain equation.
In particular, degree zero has positive sign and all negative total degrees are zero. -/
theorem moduleCup_component_chain_equation {F G : X.Modules} (D : CupResolutionPairing F G)
    (l : ∀ n : ℤ, (D.left.integerComplex ⊗ D.right.integerComplex).X n ⟶
      D.target.integerComplex.X n)
    (hl : ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V))
      (b : Γ(D.right.K.X q, V)),
      ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega)) ≫ l (p + q) ≫
        (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)) =
        D.pair p q V a b) :
    ∀ (i j : ℤ), (ComplexShape.up ℤ).Rel i j →
      l i ≫ D.target.integerComplex.d i j =
        (D.left.integerComplex ⊗ D.right.integerComplex).d i j ≫ l j
    := by
  have hformula (p q n : ℕ) (k : ℤ) (h : p + q = n) (hk : (n : ℤ) = k)
      (V : X.Opens) (a : Γ(D.left.K.X p, V)) (b : Γ(D.right.K.X q, V)) :
      (HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          (p : ℤ) (q : ℤ) k (by omega) ≫ l k ≫
        (D.target.K.extendXIso ComplexShape.embeddingUpNat hk).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat rfl).inv.val.app (op V) b)) =
        (eqToHom (congrArg (fun n ↦ D.target.K.X n) h)).val.app (op V)
          (D.pair p q V a b) := by
    subst n
    subst k
    simp only [eqToHom_refl, val_id_apply]
    exact hl p q V a b
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hi : p + q = i := hpq
  subst i
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · lift p to ℕ using hp
      lift q to ℕ using hq
      simp only [ComplexShape.π_def]
      erw [reassoc_of% (tensor_d (X := X) D.left.integerComplex
        D.right.integerComplex (p : ℤ) (q : ℤ))]
      rw [← cancel_epi
        ((D.left.K.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv ⊗ₘ
          (D.right.K.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv)]
      rw [← cancel_mono
        (D.target.K.extendXIso ComplexShape.embeddingUpNat (i := p + q + 1)
          (by simp)).hom]
      rw [D.target.K.extend_d_eq ComplexShape.embeddingUpNat
        (i := p + q) (j := p + q + 1) (by simp) (by simp)]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Preadditive.comp_add, Preadditive.add_comp, Units.smul_def,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      apply tensor_hom_ext (X := X)
      intro V a b
      simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.add_app,
        AddCommGrpCat.hom_add_apply, app_zsmul_apply, tensorHom_app_tmulSection]
      simp only [app_val_apply]
      have hwL := whiskerRight_val (X := X)
        (D.left.integerComplex.d (p : ℤ) (p + 1)) V
        ((D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).inv.val.app (op V) a)
        ((D.right.K.extendXIso ComplexShape.embeddingUpNat rfl).inv.val.app (op V) b)
      have hwR := whiskerLeft_val (X := X)
        (D.right.integerComplex.d (q : ℤ) (q + 1)) V
        ((D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).inv.val.app (op V) a)
        ((D.right.K.extendXIso ComplexShape.embeddingUpNat rfl).inv.val.app (op V) b)
      erw [hwL, hwR]
      have hdL := extend_d_inv D.left.K p V a
      have hdR := extend_d_inv D.right.K q V b
      simp only [app_val_apply] at hdL hdR
      erw [hdL, hdR]
      have h₀ := hformula p q (p + q) ((p : ℤ) + q) rfl (by simp) V a b
      have h₁ := hformula (p + 1) q (p + q + 1) ((p : ℤ) + q + 1)
        (by omega) (by simp) V ((D.left.K.d p (p + 1)).val.app (op V) a) b
      have h₂ := hformula p (q + 1) (p + q + 1) ((p : ℤ) + q + 1)
        (by omega) (by simp) V a ((D.right.K.d q (q + 1)).val.app (op V) b)
      simp only [SheafOfModules.comp_val, eqToHom_refl, val_id_apply] at h₀ h₁ h₂
      erw [h₀, h₁, h₂]
      simpa only [Int.coe_negOnePow_natCast, Nat.add_assoc, eqToHom_refl,
        val_id_apply] using D.leibniz p q V a b
    · apply IsZero.eq_of_src
      apply (tensorLeft _).map_isZero
      exact D.right.K.isZero_extend_X ComplexShape.embeddingUpNat q (by
        intro n hn
        change (n : ℤ) = q at hn
        omega)
  · apply IsZero.eq_of_src
    apply (tensorRight _).map_isZero
    exact D.left.K.isZero_extend_X ComplexShape.embeddingUpNat p (by
      intro n hn
      change (n : ℤ) = p at hn
      omega)

end
end AlgebraicGeometry.Scheme.Modules
