import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Periodic automorphisms of compatible left quotients

A continuous group automorphism of finite order has Haar modulus one. If it
preserves a closed subgroup, its restriction has modulus one as well, so the
induced quotient homeomorphism and its inverse preserve every compatible measure.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uG

section Generic

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The `k`-fold composite of a continuous multiplicative automorphism. -/
def iterateEquiv (φ : H ≃ₜ* H) : ℕ → (H ≃ₜ* H)
  | 0 => ContinuousMulEquiv.refl H
  | k + 1 => (iterateEquiv φ k).trans φ

theorem iterateEquiv_apply (φ : H ≃ₜ* H) (k : ℕ) (x : H) :
    iterateEquiv φ k x = φ^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change φ (iterateEquiv φ k x) = _
    rw [ih]

variable [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

theorem mulEquivHaarChar_iterateEquiv (φ : H ≃ₜ* H) (k : ℕ) :
    mulEquivHaarChar (iterateEquiv φ k) = mulEquivHaarChar φ ^ k := by
  induction k with
  | zero => exact mulEquivHaarChar_refl
  | succ k ih =>
    change mulEquivHaarChar ((iterateEquiv φ k).trans φ) = _
    rw [mulEquivHaarChar_trans, ih, pow_succ]

/-- A continuous automorphism with a positive iterate equal to the identity has Haar
character `1`. -/
theorem mulEquivHaarChar_eq_one_of_iterate (φ : H ≃ₜ* H) {m : ℕ} (hm : m ≠ 0)
    (hφ : ∀ x, φ^[m] x = x) : mulEquivHaarChar φ = 1 := by
  have h : iterateEquiv φ m = ContinuousMulEquiv.refl H := by
    ext x
    rw [iterateEquiv_apply, hφ]
    rfl
  have hpow : mulEquivHaarChar φ ^ m = 1 := by
    rw [← mulEquivHaarChar_iterateEquiv, h, mulEquivHaarChar_refl]
  exact (pow_eq_one_iff_of_nonneg zero_le hm).mp hpow

/-- Under the hypothesis of `mulEquivHaarChar_eq_one_of_iterate`, the automorphism preserves
every regular Haar measure. -/
theorem measurePreserving_of_iterate (φ : H ≃ₜ* H) {m : ℕ} (hm : m ≠ 0)
    (hφ : ∀ x, φ^[m] x = x) (ρ : Measure H) [ρ.IsHaarMeasure] [ρ.Regular] :
    MeasurePreserving φ ρ ρ := by
  refine ⟨φ.continuous.measurable, ?_⟩
  have h := mulEquivHaarChar_smul_map ρ φ
  rwa [mulEquivHaarChar_eq_one_of_iterate φ hm hφ, one_smul] at h

end Generic

/-- A periodic ambient automorphism preserving a closed subgroup gives
measure-preserving forward and inverse maps for the supplied compatible measure. -/
def PeriodicQuotientAutomorphismPreservation : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H] {μG : Measure G} {μH : Measure H}
      [IsHaarMeasure μG] [μG.Regular] [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
      {ν : Measure (LeftQuotient H)}, IsCompatible H μG μH ν →
    ∀ (α : G ≃ₜ* G) (hHα : ∀ g : G, α g ∈ H ↔ g ∈ H)
      {d : ℕ}, d ≠ 0 → (∀ g : G, (⇑α)^[d] g = g) →
      let e := quotientAutomorphism H α hHα
      MeasurePreserving e ν ν ∧ MeasurePreserving e.symm ν ν

/-- The restriction inherits periodicity, so both moduli in the quotient
change-of-variables formula are one. -/
theorem periodicQuotientAutomorphismPreservation :
    PeriodicQuotientAutomorphismPreservation.{uG} := by
  intro G _ _ _ _ _ _ _ H hH _ _ μG μH _ _ _ _ _ _ _ ν hν α hHα d hd hα
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let β := subgroupAutomorphism H α hHα
  have hsemiconj : Function.Semiconj (H.subtype : H → G) (⇑β) (⇑α) := fun _ => rfl
  have hβ (g : H) : (⇑β)^[d] g = g :=
    Subtype.ext ((hsemiconj.iterate_right d g).trans (hα g))
  let e := quotientAutomorphism H α hHα
  have hmap : Measure.map e ν = ν := by
    rw [hν.map_quotientAutomorphism H hH α hHα, mulEquivHaarChar_eq_one_of_iterate α hd hα,
      mulEquivHaarChar_eq_one_of_iterate β hd hβ]
    simp
  have he : MeasurePreserving e ν ν := ⟨e.continuous.measurable, hmap⟩
  exact ⟨he, MeasurePreserving.symm e.toMeasurableEquiv he⟩

end Langlands.QuotientIntegration
