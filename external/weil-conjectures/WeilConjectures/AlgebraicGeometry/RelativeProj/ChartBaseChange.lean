/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Coefficientwise base change of graded algebras and homogeneous localization

Let `R → S` be a ring map, `𝒜` a graded `R`-algebra on `A` and `ℬ` a graded `S`-algebra on `B`.
A graded ring homomorphism `φ: 𝒜 →+*ᵍ ℬ` which is `R`-linear is a *coefficientwise base change*
(`GradedRingHom.IsGradedBaseChange`) if for every `n` the induced map `𝒜 n → ℬ n` exhibits
`ℬ n` as `S ⊗[R] 𝒜 n`. The typical examples are the localization `A → A[1/f]` for `f ∈ R`
(with `S = R[1/f]`) and `A → S ⊗[R] A`.

We show that in this situation the induced map on degree-zero homogeneous localizations
`Away 𝒜 s → Away ℬ (φ s)` is again a base change along `R → S`, i.e.
`S ⊗[R] (A_{(s)})₀ ≅ (B_{(φ s)})₀`.

## Main definitions and results

- `GradedRingHom.degreeLinearMap` — the `R`-linear degree-`n` part of `φ`.
- `GradedRingHom.IsGradedBaseChange` — coefficientwise base change.
- `GradedRingHom.IsGradedBaseChange.irrelevant_le` — the irrelevant ideal condition needed for
  `Proj.map`.
- `GradedRingHom.IsGradedBaseChange.isBaseChange_awayMap` — the chart rings form a base change.

## Implementation details

The proof identifies `(A_{(s)})₀` with the filtered colimit of the `𝒜 (k • d)` along
multiplication by `s` and uses that tensor products commute with this colimit; this is carried
out by hand.
-/

@[expose] public section

open TensorProduct HomogeneousLocalization

namespace HomogeneousLocalization.Away

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {s : A} {d : ℕ} (hs : s ∈ 𝒜 d)

/-- The `R`-linear map `𝒜 (k • d) → Away 𝒜 s`, `a ↦ a / s ^ k`. -/
noncomputable def mkLinearMap (k : ℕ) : 𝒜 (k • d) →ₗ[R] Away 𝒜 s where
  toFun a := Away.mk 𝒜 hs k a a.2
  map_add' a b := by
    apply val_injective
    simp only [Away.val_mk, Submodule.coe_add, val_add, Localization.add_mk_self]
  map_smul' r a := by
    apply val_injective
    simp only [Away.val_mk, Submodule.coe_smul, RingHom.id_apply, val_smul,
      Localization.smul_mk]

@[simp]
lemma mkLinearMap_apply (k : ℕ) (a : 𝒜 (k • d)) :
    mkLinearMap 𝒜 hs k a = Away.mk 𝒜 hs k a a.2 :=
  rfl

/-- Multiplication by `s ^ m` as an `R`-linear map `𝒜 (k • d) → 𝒜 (n • d)` for `k + m = n`. -/
def mulPowLinearMap (k m n : ℕ) (hn : k + m = n) : 𝒜 (k • d) →ₗ[R] 𝒜 (n • d) where
  toFun a := ⟨a * s ^ m, by
    rw [← hn, add_smul]; exact SetLike.mul_mem_graded a.2 (SetLike.pow_mem_graded m hs)⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' r a := Subtype.ext (by simp [Algebra.smul_mul_assoc])

@[simp]
lemma coe_mulPowLinearMap_apply (k m n : ℕ) (hn : k + m = n) (a : 𝒜 (k • d)) :
    (mulPowLinearMap 𝒜 hs k m n hn a : A) = a * s ^ m :=
  rfl

lemma mkLinearMap_comp_mulPowLinearMap (k m n : ℕ) (hn : k + m = n) :
    mkLinearMap 𝒜 hs n ∘ₗ mulPowLinearMap 𝒜 hs k m n hn = mkLinearMap 𝒜 hs k := by
  subst hn
  refine LinearMap.ext fun a ↦ ?_
  exact Away.mk_mul_pow_cancel 𝒜 hs k m a a.2 _

end HomogeneousLocalization.Away

namespace GradedRingHom

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]

/-- The `R`-linear map `𝒜 n → ℬ n` induced by an `R`-linear graded ring homomorphism. -/
def degreeLinearMap (φ : 𝒜 →+*ᵍ ℬ) (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (n : ℕ) : 𝒜 n →ₗ[R] ℬ n where
  toFun a := ⟨φ a, φ.map_mem a.2⟩
  map_add' a b := Subtype.ext (map_add φ _ _)
  map_smul' r a := Subtype.ext <| by
    change φ (r • (a : A)) = r • φ a
    rw [Algebra.smul_def, map_mul, hφ, ← Algebra.smul_def]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
@[simp]
lemma coe_degreeLinearMap_apply (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r) (n : ℕ) (a : 𝒜 n) :
    (φ.degreeLinearMap hφ n a : B) = φ a :=
  rfl

/-- A graded ring homomorphism `φ : 𝒜 →+*ᵍ ℬ` from a graded `R`-algebra to a graded `S`-algebra
is a *coefficientwise base change* along `R → S` if it is `R`-linear and every degree-`n`
component `𝒜 n → ℬ n` exhibits `ℬ n` as `S ⊗[R] 𝒜 n`. -/
structure IsGradedBaseChange (φ : 𝒜 →+*ᵍ ℬ) : Prop where
  map_algebraMap : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r
  isBaseChange : ∀ n, IsBaseChange S (φ.degreeLinearMap map_algebraMap n)

section Away

variable (φ : 𝒜 →+*ᵍ ℬ) (s : A)

/-- The `R`-algebra structure on the target chart ring `Away ℬ (φ s)`, obtained by restricting
scalars along `R → S`. -/
@[reducible] noncomputable def awayAlgebra : Algebra R (Away ℬ (φ s)) :=
  Algebra.compHom _ (algebraMap R S)

/-- The algebra structure `Away 𝒜 s → Away ℬ (φ s)` given by `HomogeneousLocalization.Away.map`.
-/
@[reducible] noncomputable def awayMapAlgebra : Algebra (Away 𝒜 s) (Away ℬ (φ s)) :=
  (Away.map φ s).toAlgebra

attribute [local instance] awayAlgebra awayMapAlgebra

omit [Algebra R B] [IsScalarTower R S B] [GradedAlgebra 𝒜] in
lemma awayAlgebra_isScalarTower : IsScalarTower R S (Away ℬ (φ s)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable {φ} in
lemma awayMapAlgebra_isScalarTower (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r) :
    IsScalarTower R (Away 𝒜 s) (Away ℬ (φ s)) := by
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  change _ = Away.map φ s (fromZeroRingHom 𝒜 _ (algebraMap R (𝒜 0) r))
  rw [← RingHom.comp_apply, HomogeneousLocalization.Away.map_comp_fromZeroRingHom]
  apply val_injective
  simp only [RingHom.comp_apply, HomogeneousLocalization.val_fromZeroRingHom,
    coe_gradeZeroRingHom_apply, SetLike.GradeZero.coe_algebraMap, hφ]
  rw [show algebraMap R (Away ℬ (φ s)) r = algebraMap S _ (algebraMap R S r) from rfl,
    val_algebraMap, IsScalarTower.algebraMap_apply R S B]

variable {φ} in
/-- The induced map of chart rings `Away 𝒜 s → Away ℬ (φ s)` as an `R`-linear map. -/
noncomputable def awayLinearMap (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r) :
    Away 𝒜 s →ₗ[R] Away ℬ (φ s) :=
  haveI := awayMapAlgebra_isScalarTower s hφ
  (IsScalarTower.toAlgHom R (Away 𝒜 s) (Away ℬ (φ s))).toLinearMap

@[simp]
lemma awayLinearMap_apply (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (x : Away 𝒜 s) : awayLinearMap s hφ x = Away.map φ s x :=
  rfl

end Away

namespace IsGradedBaseChange

variable {φ : 𝒜 →+*ᵍ ℬ} (h : φ.IsGradedBaseChange)
include h

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- Every homogeneous element of `ℬ` of degree `n` is an `S`-linear combination of images of
homogeneous elements of `𝒜` of degree `n`. -/
lemma mem_span (n : ℕ) {b : B} (hb : b ∈ ℬ n) :
    b ∈ Submodule.span S (φ '' (𝒜 n : Set A)) := by
  suffices ∀ x : ℬ n, (x : B) ∈ Submodule.span S (φ '' (𝒜 n : Set A)) from this ⟨b, hb⟩
  intro x
  induction x using (h.isBaseChange n).inductionOn with
  | tmul a => exact Submodule.subset_span ⟨a, a.2, rfl⟩
  | smul c x hx => exact Submodule.smul_mem _ c hx
  | add x y hx hy => exact add_mem hx hy

/-- The irrelevant ideal condition for `Proj.map` holds for a coefficientwise base change. -/
lemma irrelevant_le :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi b hb
  change b ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ
  have key : Submodule.span S (φ '' (𝒜 i : Set A)) ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ).restrictScalars S := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi ha)
  exact key (h.mem_span i hb)

variable {s : A} {d : ℕ} (hs : s ∈ 𝒜 d)

attribute [local instance] awayAlgebra awayMapAlgebra awayAlgebra_isScalarTower

/-- The chart comparison map `S ⊗[R] Away 𝒜 s → Away ℬ (φ s)`. -/
private noncomputable abbrev chartMap : S ⊗[R] Away 𝒜 s →ₗ[S] Away ℬ (φ s) :=
  (awayLinearMap s h.map_algebraMap).liftBaseChange S

/-- The base change isomorphism in degree `n`. -/
private noncomputable abbrev degEquiv (n : ℕ) : S ⊗[R] 𝒜 n ≃ₗ[S] ℬ n :=
  (h.isBaseChange n).equiv

private lemma chartMap_baseChange_mkLinearMap (k : ℕ) (y : S ⊗[R] 𝒜 (k • d)) :
    chartMap h ((Away.mkLinearMap 𝒜 hs k).baseChange S y) =
      Away.mkLinearMap ℬ (φ.map_mem hs) k (degEquiv h (k • d) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul c a =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, IsBaseChange.equiv_tmul,
      map_smul, Away.mkLinearMap_apply, awayLinearMap_apply, Away.map_mk]
    rfl
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

private lemma degEquiv_comp_baseChange_mulPowLinearMap (k m n : ℕ) (hn : k + m = n) :
    (degEquiv h (n • d)).toLinearMap ∘ₗ (Away.mulPowLinearMap 𝒜 hs k m n hn).baseChange S =
      Away.mulPowLinearMap ℬ (φ.map_mem hs) k m n hn ∘ₗ (degEquiv h (k • d)).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun c a ↦ ?_
  apply Subtype.ext
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, IsBaseChange.equiv_tmul, map_smul, Submodule.coe_smul,
    Away.coe_mulPowLinearMap_apply, coe_degreeLinearMap_apply, map_mul, map_pow]
  rfl

omit h in
private lemma exists_baseChange_mkLinearMap (x : S ⊗[R] Away 𝒜 s) :
    ∃ (k : ℕ) (y : S ⊗[R] 𝒜 (k • d)), (Away.mkLinearMap 𝒜 hs k).baseChange S y = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c z =>
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs z
    exact ⟨n, c ⊗ₜ ⟨a, ha⟩, rfl⟩
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨k, y₁, rfl⟩ := h₁
    obtain ⟨l, y₂, rfl⟩ := h₂
    refine ⟨k + l, (Away.mulPowLinearMap 𝒜 hs k l (k + l) rfl).baseChange S y₁ +
      (Away.mulPowLinearMap 𝒜 hs l k (k + l) (add_comm l k)).baseChange S y₂, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, Away.mkLinearMap_comp_mulPowLinearMap,
      Away.mkLinearMap_comp_mulPowLinearMap]

include hs in
private lemma chartMap_bijective : Function.Bijective (chartMap (s := s) h) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨k, y, rfl⟩ := exists_baseChange_mkLinearMap hs x
    rw [chartMap_baseChange_mkLinearMap h hs] at hx
    have hx' : Localization.mk ((degEquiv h (k • d) y : ℬ (k • d)) : B)
        (⟨φ s ^ k, k, rfl⟩ : Submonoid.powers (φ s)) = 0 := by
      rw [← val_zero (𝒜 := ℬ) (x := Submonoid.powers (φ s))]; exact congrArg val hx
    rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hx'
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := hx'
    have hz : (Away.mulPowLinearMap 𝒜 hs k j (k + j) rfl).baseChange S y = 0 := by
      apply (degEquiv h ((k + j) • d)).injective
      have := LinearMap.congr_fun (degEquiv_comp_baseChange_mulPowLinearMap h hs k j _ rfl) y
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
      rw [this, map_zero]
      apply Subtype.ext
      simp only [Away.coe_mulPowLinearMap_apply, Submodule.coe_zero]
      rw [mul_comm]
      exact hj
    rw [← Away.mkLinearMap_comp_mulPowLinearMap 𝒜 hs k j (k + j) rfl, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hz, map_zero]
  · intro z
    obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (φ.map_mem hs) z
    refine ⟨(Away.mkLinearMap 𝒜 hs n).baseChange S ((degEquiv h (n • d)).symm ⟨b, hb⟩), ?_⟩
    rw [chartMap_baseChange_mkLinearMap h hs, LinearEquiv.apply_symm_apply]
    rfl

include hs in
/-- **Chart rings commute with coefficientwise base change**: for `s ∈ 𝒜 d`, the square
`R → S`, `R → Away 𝒜 s → Away ℬ (φ s)` is a pushout, i.e.
`S ⊗[R] (A_{(s)})₀ ≅ (B_{(φ s)})₀`, `c ⊗ (a / s ^ m) ↦ c • φ a / φ s ^ m`. -/
theorem isPushout_away :
    haveI := awayMapAlgebra_isScalarTower s h.map_algebraMap
    Algebra.IsPushout R S (Away 𝒜 s) (Away ℬ (φ s)) := by
  have := awayMapAlgebra_isScalarTower s h.map_algebraMap
  exact ⟨IsBaseChange.of_equiv (f := awayLinearMap s h.map_algebraMap)
    (LinearEquiv.ofBijective _ (chartMap_bijective h hs)) fun x ↦ by simp⟩

end IsGradedBaseChange

end GradedRingHom
