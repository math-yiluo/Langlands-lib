import Langlands.CommutativeAlgebra.GradedLineGlobal
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # The coordinate-degree component and the identity cotangent module -/

noncomputable section

universe u

open Polynomial
open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.GradedLine

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {c : A →+* LaurentPolynomial A} (hc : IsGrading R c)

attribute [local instance] quotientField

/-- Universal line fibres force the coordinate-degree component to generate the algebra. -/
theorem adjoin_homog_eq_top [Algebra.FiniteType R A]
    (hneg : ∀ a, ∀ n < 0, (c a).coeff n = 0)
    (hzero : ∀ a, (c a).coeff 0 ∈ Set.range (algebraMap R A))
    {d : ℕ} (hd : 0 < d)
    (hfib : ∀ (p : Ideal R) [p.IsMaximal], ∃ ψ : A →ₐ[R] (R ⧸ p)[X],
      IsFibreLine hc (R ⧸ p) d ψ ∧
        ∀ a, ψ a = 0 → a ∈ p.map (algebraMap R A)) :
    Algebra.adjoin R (homog hc d : Set A) = ⊤ := by
  classical
  let S := Algebra.adjoin R (homog hc d : Set A)
  have hle (n : ℤ) : homog hc n ≤ S.toSubmodule := by
    apply le_of_all_maximal_le_sup_smul (homog_fg hc hneg hzero n)
    intro p hp
    let := hp
    obtain ⟨ψ, hψ, hker⟩ := hfib p
    obtain ⟨a, ha⟩ := hψ.exists_coeff_one_ne_zero
    have hpow : powSpan (comp hc d a) d n ≤ S.toSubmodule := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, -, rfl⟩
      exact S.pow_mem (Algebra.subset_adjoin (comp_mem_homog hc d a)) j
    exact (le_powSpan_sup_of_surjective hc hψ hd Ideal.Quotient.mk_surjective p hker
      (comp_mem_homog hc d a) ha n).trans (sup_le_sup_right hpow _)
  apply top_unique
  intro a _
  change a ∈ S
  rw [← sum_comp hc a]
  exact S.sum_mem fun n _ => hle n (comp_mem_homog hc n a)

section Augmentation

variable (ε : A →ₐ[R] R)
  (hε : ∀ a, comp hc 0 a = algebraMap R A (ε a))

include hε in
/-- A positive homogeneous element has zero augmentation. -/
theorem augmentation_eq_zero_of_homogeneous {d : ℤ} (hd : d ≠ 0)
    {a : A} (ha : a ∈ homog hc d) : ε a = 0 := by
  have heq := hε a
  rw [comp_of_mem hc ha, ite_eq_right (Ne.symm hd)] at heq
  have := congrArg ε heq
  simpa only [map_zero, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    using this.symm

include hε in
/-- On an algebra generated in one positive degree, the corresponding component
satisfies the identity-point Leibniz rule. -/
theorem comp_mul_of_adjoin_homog {d : ℕ} (hd : 0 < d)
    (hgen : Algebra.adjoin R (homog hc d : Set A) = ⊤) (a b : A) :
    comp hc d (a * b) = ε a • comp hc d b + ε b • comp hc d a := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have ha : a ∈ Algebra.adjoin R (homog hc d : Set A) := by rw [hgen]; trivial
  induction ha using Algebra.adjoin_induction generalizing b with
  | mem x hx =>
    rw [comp_mul_of_mem hc hx, sub_self, hε b, comp_self hc hx,
      augmentation_eq_zero_of_homogeneous hc ε hε hd0 hx, zero_smul, zero_add,
      Algebra.smul_def, mul_comm]
  | algebraMap r =>
    rw [← Algebra.smul_def, map_smul, ε.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, comp_algebraMap, ite_eq_right hd0, smul_zero, add_zero]
  | add x y _ _ hx hy =>
    rw [add_mul, map_add, hx, hy, map_add, add_smul, map_add, smul_add]
    abel
  | mul x y _ _ hx hy =>
    rw [mul_assoc, hx, hy, map_mul, hx y]
    simp only [smul_add, smul_smul]
    simp only [Algebra.smul_def, map_mul]
    ring

end Augmentation

section Cotangent

variable [Algebra A R] [IsScalarTower R A R]
  (hε : ∀ a, comp hc 0 a = algebraMap R A (algebraMap A R a))

local notation "ε" => IsScalarTower.toAlgHom R A R

local instance degreeAugmentationModule (d : ℤ) : Module A (homog hc d) :=
  Module.compHom (homog hc d) (algebraMap A R)

local instance degreeAugmentationTower (d : ℤ) : IsScalarTower A R (homog hc d) :=
  ⟨fun a r x => by
    rw [Algebra.smul_def]
    change (algebraMap A R a * r) • x = algebraMap A R a • r • x
    exact mul_smul _ _ _⟩

local instance degreeBaseTower (d : ℤ) : IsScalarTower R A (homog hc d) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change algebraMap A R (algebraMap R A r) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R A R, Algebra.algebraMap_self, RingHom.id_apply]

/-- The coordinate-degree component, with its augmentation action, is a derivation. -/
def degreeDerivation {d : ℕ} (hd : 0 < d)
    (hgen : Algebra.adjoin R (homog hc d : Set A) = ⊤) :
    Derivation R A (homog hc d) where
  toLinearMap := (comp hc d).codRestrict (homog hc d) (comp_mem_homog hc d)
  map_one_eq_zero' := by
    apply Subtype.ext
    change comp hc d 1 = 0
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    simpa only [map_one, ite_eq_right hd0] using
      comp_algebraMap hc (d : ℤ) (1 : R)
  leibniz' a b := by
    apply Subtype.ext
    exact comp_mul_of_adjoin_homog hc ε hε hd hgen a b

/-- Differentiating a homogeneous coordinate and pulling back by the augmentation. -/
def degreeToCotangent (d : ℤ) :
    homog hc d →ₗ[R] R ⊗[A] KaehlerDifferential R A :=
  ((TensorProduct.mk A R (KaehlerDifferential R A) 1).restrictScalars R).comp
    ((KaehlerDifferential.DLinearMap R A).comp (homog hc d).subtype)

/-- The coordinate-degree component is the actual cotangent module at the augmentation. -/
def degreeCotangentEquiv {d : ℕ} (hd : 0 < d)
    (hgen : Algebra.adjoin R (homog hc d : Set A) = ⊤) :
    homog hc d ≃ₗ[R] R ⊗[A] KaehlerDifferential R A := by
  let f := degreeToCotangent hc (d : ℤ)
  let D := degreeDerivation hc hε hd hgen
  let g := D.liftKaehlerDifferential.liftBaseChange R
  have hgf : ∀ x, g (f x) = x := by
    intro x
    change D.liftKaehlerDifferential.liftBaseChange R
      (1 ⊗ₜ KaehlerDifferential.D R A (x : A)) = x
    rw [LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]
    apply Subtype.ext
    exact comp_self hc x.property
  have hfg : ∀ x, f (g x) = x := by
    let fA : homog hc d →ₗ[A] R ⊗[A] KaehlerDifferential R A := f.restrictScalars A
    have he : fA.comp D.liftKaehlerDifferential =
        TensorProduct.mk A R (KaehlerDifferential R A) 1 := by
      apply Derivation.liftKaehlerDifferential_unique
      apply Derivation.ext_of_adjoin_eq_top (homog hc d : Set A) hgen
      intro a ha
      change f (D.liftKaehlerDifferential (KaehlerDifferential.D R A a)) =
        1 ⊗ₜ KaehlerDifferential.D R A a
      rw [Derivation.liftKaehlerDifferential_comp_D]
      change 1 ⊗ₜ KaehlerDifferential.D R A (comp hc d a) = _
      rw [comp_self hc ha]
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r w =>
      change f (r • D.liftKaehlerDifferential w) = r ⊗ₜ w
      rw [map_smul]
      have hw := LinearMap.congr_fun he w
      change f (D.liftKaehlerDifferential w) = 1 ⊗ₜ w at hw
      rw [hw, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact LinearEquiv.ofLinearMap f g (LinearMap.ext hfg) (LinearMap.ext hgf)

end Cotangent

end Langlands.CommutativeAlgebra.GradedLine
