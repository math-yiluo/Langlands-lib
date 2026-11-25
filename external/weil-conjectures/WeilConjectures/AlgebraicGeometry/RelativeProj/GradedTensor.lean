/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Affine

/-!
# Coefficientwise base change of graded algebras: tensor products

This file collects algebraic facts about coefficientwise base change of graded algebras
(`GradedRingHom.IsGradedBaseChange`), used to construct pullbacks of quasi-coherent graded
algebras.

## Main results

- `GradedRingHom.IsGradedBaseChange.isBaseChange_linearMap` — a coefficientwise base change is a
  base change of the underlying modules, i.e. `B ≅ S ⊗[R] A`.
- `GradedRingHom.baseChangeMap` and `GradedRingHom.isGradedBaseChangeAlong_baseChangeMap` — for an
  `R`-algebra map `T → T'`, the map `T ⊗[R] A → T' ⊗[R] A` is a coefficientwise base change.
- `GradedRingHom.IsGradedBaseChange.lift` and
  `GradedRingHom.IsGradedBaseChange.isGradedBaseChangeAlong_lift` — if `B ≅ S ⊗[R] A`
  coefficientwise, then any `R`-algebra map `S → T` induces a coefficientwise base change
  `B → T ⊗[R] A`.
-/

@[expose] public section

open TensorProduct

namespace GradedRingHom

section IsBaseChangeLinear

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]

/-- An `R`-linear graded ring homomorphism, as an `R`-linear map. -/
def toLinearMap' (φ : 𝒜 →+*ᵍ ℬ) (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r) :
    A →ₗ[R] B where
  toFun := φ
  map_add' := map_add φ
  map_smul' r a := by
    rw [Algebra.smul_def, map_mul, hφ, ← Algebra.smul_def]
    rfl

omit [Algebra R S] [IsScalarTower R S B] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
@[simp]
lemma toLinearMap'_apply (φ : 𝒜 →+*ᵍ ℬ) (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (a : A) : φ.toLinearMap' hφ a = φ a :=
  rfl

/-- A coefficientwise base change is a base change of the underlying modules: `B ≅ S ⊗[R] A`. -/
theorem IsGradedBaseChange.isBaseChange_linearMap {φ : 𝒜 →+*ᵍ ℬ} (h : φ.IsGradedBaseChange) :
    IsBaseChange S (φ.toLinearMap' h.map_algebraMap) := by
  classical
  have h1 : IsBaseChange S (DirectSum.lmap fun n ↦ φ.degreeLinearMap h.map_algebraMap n) :=
    IsBaseChange.directSum fun n ↦ h.isBaseChange n
  refine (IsBaseChange.iff_of_equiv_comm (DirectSum.decomposeLinearEquiv 𝒜).symm
    (DirectSum.decomposeLinearEquiv ℬ).symm ?_).mp h1
  refine DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_symm_lof, toLinearMap'_apply, LinearEquiv.restrictScalars_apply,
    DirectSum.lmap_lof]
  rw [DirectSum.lof_eq_of, DirectSum.decomposeLinearEquiv_symm_apply, DirectSum.decompose_symm_of]
  rfl

end IsBaseChangeLinear

section BaseChangeMap

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] (T : Type*) [CommRing T] [Algebra R T] {T' : Type*} [CommRing T']
  [Algebra R T']

/-- The degree-wise inclusion `𝒜 n → T ⊗[R] 𝒜 n`, `a ↦ 1 ⊗ a`. -/
def baseChangeIncl (n : ℕ) : 𝒜 n →ₗ[R] (𝒜 n).baseChange T where
  toFun a := ⟨1 ⊗ₜ (a : A), Submodule.tmul_mem_baseChange_of_mem _ a.2⟩
  map_add' a b := Subtype.ext (tmul_add _ _ _)
  map_smul' r a := Subtype.ext (by simp)

omit [GradedAlgebra 𝒜] in
@[simp]
lemma coe_baseChangeIncl_apply (n : ℕ) (a : 𝒜 n) :
    (baseChangeIncl 𝒜 T n a : T ⊗[R] A) = 1 ⊗ₜ (a : A) :=
  rfl

lemma isBaseChange_baseChangeIncl (n : ℕ) : IsBaseChange T (baseChangeIncl 𝒜 T n) :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective ((𝒜 n).toBaseChange T)
    (DirectSum.toBaseChange_bijective 𝒜 n)) fun _ ↦ rfl

variable {T}

/-- For an `R`-algebra map `ψ : T → T'`, the graded ring homomorphism
`T ⊗[R] A → T' ⊗[R] A`. -/
noncomputable def baseChangeMap (ψ : T →ₐ[R] T') :
    (fun n ↦ (𝒜 n).baseChange T) →+*ᵍ (fun n ↦ (𝒜 n).baseChange T') where
  __ := (Algebra.TensorProduct.map ψ (AlgHom.id R A)).toRingHom
  map_mem {n x} hx := by
    obtain ⟨y, rfl⟩ := Submodule.toBaseChange_surjective' T (𝒜 n) hx
    clear hx
    induction y using TensorProduct.inductionOn with
    | tmul t a =>
      simpa using Submodule.tmul_mem_baseChange_of_mem (ψ t) a.2
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add] at h₁ h₂ ⊢
      rw [Submodule.coe_add, map_add]
      exact add_mem h₁ h₂

omit [GradedAlgebra 𝒜] in
@[simp]
lemma baseChangeMap_tmul (ψ : T →ₐ[R] T') (t : T) (a : A) :
    baseChangeMap 𝒜 ψ (t ⊗ₜ a) = ψ t ⊗ₜ a :=
  rfl

/-- The map `T ⊗[R] A → T' ⊗[R] A` induced by `T → T'` is a coefficientwise base change. -/
theorem isGradedBaseChange_baseChangeMap [Algebra T T'] [IsScalarTower R T T'] :
    (baseChangeMap 𝒜 (IsScalarTower.toAlgHom R T T')).IsGradedBaseChange := by
  refine ⟨fun t ↦ rfl, fun n ↦ ?_⟩
  refine IsBaseChange.of_comp (isBaseChange_baseChangeIncl 𝒜 T n) ?_
  convert isBaseChange_baseChangeIncl 𝒜 T' n using 1
  ext a
  simp [degreeLinearMap]

end BaseChangeMap

section Lift

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]
  {φ : 𝒜 →+*ᵍ ℬ} (h : φ.IsGradedBaseChange)
  (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

namespace IsGradedBaseChange

omit [GradedAlgebra 𝒜] in
include h in
/-- A ring homomorphism out of `B` is determined by its values on `φ(A)` and on the image of
`S`. -/
lemma ringHom_ext {Q : Type*} [Semiring Q] {u v : B →+* Q} (h₁ : ∀ a, u (φ a) = v (φ a))
    (h₂ : ∀ s, u (algebraMap S B s) = v (algebraMap S B s)) : u = v := by
  classical
  ext b
  rw [← DirectSum.sum_support_decompose ℬ b, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  suffices ∀ c ∈ Submodule.span S (φ '' (𝒜 n : Set A)), u c = v c from
    this _ (h.mem_span n (DirectSum.decompose ℬ b n).2)
  intro c hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    exact h₁ a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul s x _ hx => simp [Algebra.smul_def, hx, h₂]

/-- If `φ : 𝒜 →+*ᵍ ℬ` is a coefficientwise base change along `R → S`, then for every `S`-algebra
`T`, the induced homomorphism `B = S ⊗[R] A → T ⊗[R] A`. -/
noncomputable def liftAlgHom : B →ₐ[R] T ⊗[R] A :=
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R S A B := ⟨h.isBaseChange_linearMap⟩
  Algebra.pushoutDesc B
    ((Algebra.TensorProduct.includeLeft (S := R)).comp (IsScalarTower.toAlgHom R S T))
    Algebra.TensorProduct.includeRight fun _ _ ↦ mul_comm _ _

lemma liftAlgHom_algebraMap (s : S) :
    h.liftAlgHom T (algebraMap S B s) = algebraMap S T s ⊗ₜ 1 :=
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R S A B := ⟨h.isBaseChange_linearMap⟩
  Algebra.pushoutDesc_left _ _ _ _ s

lemma liftAlgHom_apply (a : A) : h.liftAlgHom T (φ a) = 1 ⊗ₜ a :=
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R S A B := ⟨h.isBaseChange_linearMap⟩
  Algebra.pushoutDesc_right _ _ _ _ a

lemma liftAlgHom_smul_apply (s : S) (a : A) :
    h.liftAlgHom T (s • φ a) = algebraMap S T s ⊗ₜ a := by
  rw [Algebra.smul_def, map_mul, liftAlgHom_algebraMap, liftAlgHom_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The induced graded homomorphism `B = S ⊗[R] A → T ⊗[R] A`. -/
noncomputable def lift : ℬ →+*ᵍ (fun n ↦ (𝒜 n).baseChange T) where
  __ := (h.liftAlgHom T).toRingHom
  map_mem {n b} hb := by
    change h.liftAlgHom T b ∈ (𝒜 n).baseChange T
    have hb' := h.mem_span n hb
    clear hb
    induction hb' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [liftAlgHom_apply]
      exact Submodule.tmul_mem_baseChange_of_mem _ ha
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul s x _ hx =>
      rw [Algebra.smul_def, map_mul, liftAlgHom_algebraMap,
        show algebraMap S T s ⊗ₜ[R] (1 : A) = algebraMap T (T ⊗[R] A) (algebraMap S T s) from rfl,
        ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx

lemma lift_apply (b : B) : h.lift T b = h.liftAlgHom T b :=
  rfl

/-- The induced map `B = S ⊗[R] A → T ⊗[R] A` is a coefficientwise base change along `S → T`. -/
theorem isGradedBaseChange_lift : (h.lift T).IsGradedBaseChange := by
  refine ⟨fun s ↦ h.liftAlgHom_algebraMap T s, fun n ↦ ?_⟩
  refine IsBaseChange.of_comp (h.isBaseChange n) ?_
  convert isBaseChange_baseChangeIncl 𝒜 T n using 1
  ext a
  simp [degreeLinearMap, lift_apply, liftAlgHom_apply]

end IsGradedBaseChange

end Lift

end GradedRingHom
