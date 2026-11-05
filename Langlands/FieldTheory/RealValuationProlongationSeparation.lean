import Langlands.FieldTheory.RealValuationProlongationExistence
import Mathlib.Analysis.AbsoluteValue.Equivalence

/-! # Separation of distinct normalized real valuation prolongations -/

noncomputable section

open scoped NNReal

namespace Langlands.FieldTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Equivalent real prolongations of the same nontrivial valuation are equal:
the original normalization fixes the real exponent relating equivalent valuations. -/
theorem normalizedRealProlongations_eq_of_equiv (ν : Valuation K ℝ≥0)
    (hν : ν.IsNontrivial) {w₁ w₂ : Valuation Ω ℝ≥0}
    (h₁ : w₁.comap (algebraMap K Ω) = ν)
    (h₂ : w₂.comap (algebraMap K Ω) = ν)
    (he : (realValuationAbsoluteValue w₁).IsEquiv (realValuationAbsoluteValue w₂)) :
    w₁ = w₂ := by
  obtain ⟨c, _, hc⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp he
  obtain ⟨a, ha0, ha1⟩ := hν.exists_val_nontrivial
  have h₁a : w₁ (algebraMap K Ω a) = ν a :=
    congrArg (fun v : Valuation K ℝ≥0 => v a) h₁
  have h₂a : w₂ (algebraMap K Ω a) = ν a :=
    congrArg (fun v : Valuation K ℝ≥0 => v a) h₂
  have hνpos : (0 : ℝ) < ν a := by exact_mod_cast pos_iff_ne_zero.mpr ha0
  have hνne : (ν a : ℝ) ≠ 1 := by exact_mod_cast ha1
  have hc1 : c = 1 := by
    apply (Real.rpow_right_inj hνpos hνne).mp
    have h := congrFun hc (algebraMap K Ω a)
    change (w₁ (algebraMap K Ω a) : ℝ) ^ c = w₂ (algebraMap K Ω a) at h
    simpa only [h₁a, h₂a, Real.rpow_one] using h
  apply Valuation.ext
  intro x
  apply NNReal.coe_injective
  have h := congrFun hc x
  change (w₁ x : ℝ) ^ c = (w₂ x : ℝ) at h
  simpa only [hc1, Real.rpow_one] using h

/-- A finite injective family of normalized prolongations can distinguish one
member from all the others by residues zero and one. -/
theorem exists_normalizedRealProlongation_separator {ι : Type*} [Finite ι]
    (ν : Valuation K ℝ≥0) (hν : ν.IsNontrivial)
    (w : ι → Valuation Ω ℝ≥0) (hw : Function.Injective w)
    (hres : ∀ i, (w i).comap (algebraMap K Ω) = ν) (i : ι) :
    ∃ x : Ω, w i x < 1 ∧ ∀ j, j ≠ i → w j (x - 1) < 1 := by
  classical
  have hnon : ∀ j, (realValuationAbsoluteValue (w j)).IsNontrivial := by
    intro j
    obtain ⟨a, ha0, ha1⟩ := hν.exists_val_nontrivial
    have ha : w j (algebraMap K Ω a) = ν a :=
      congrArg (fun v : Valuation K ℝ≥0 => v a) (hres j)
    refine ⟨algebraMap K Ω a, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (algebraMap K Ω).injective).mpr (ν.ne_zero_iff.mp ha0)
    · change (w j (algebraMap K Ω a) : ℝ) ≠ 1
      rw [ha]
      exact_mod_cast ha1
  have hpair : Pairwise fun j k =>
      ¬ (realValuationAbsoluteValue (w j)).IsEquiv (realValuationAbsoluteValue (w k)) := by
    intro j k hjk he
    exact hjk (hw (normalizedRealProlongations_eq_of_equiv ν hν (hres j) (hres k) he))
  obtain ⟨a, hai, haj⟩ := AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hnon hpair i
  have hai' : 1 < w i a := by exact_mod_cast hai
  have hdi : w i (1 + a) = w i a :=
    (w i).map_add_eq_of_lt_right (by simpa only [map_one] using hai')
  have hden : 1 + a ≠ 0 := (w i).ne_zero_iff.mp (by
    rw [hdi]
    exact (zero_lt_one.trans hai').ne')
  refine ⟨(1 + a)⁻¹, ?_, fun j hji => ?_⟩
  · rw [map_inv₀, hdi]
    exact inv_lt_one_of_one_lt₀ hai'
  · have haj' : w j a < 1 := by exact_mod_cast haj j hji
    have hdj : w j (1 + a) = 1 := by
      rw [(w j).map_add_eq_of_lt_left (by simpa only [map_one] using haj'), map_one]
    have heq : (1 + a)⁻¹ - 1 = -a / (1 + a) := by
      field_simp [hden]
      ring
    rw [heq, map_div₀, Valuation.map_neg, hdj, div_one]
    exact haj'

/-- A chosen element separating one normalized prolongation from a finite
family by its residue at each member. -/
def normalizedRealProlongationSeparator {ι : Type*} [Finite ι]
    (ν : Valuation K ℝ≥0) (hν : ν.IsNontrivial)
    (w : ι → Valuation Ω ℝ≥0) (hw : Function.Injective w)
    (hres : ∀ i, (w i).comap (algebraMap K Ω) = ν) (i : ι) : Ω :=
  (exists_normalizedRealProlongation_separator ν hν w hw hres i).choose

/-- The chosen separator is small at the selected prolongation and congruent
to one at every other prolongation. -/
theorem normalizedRealProlongationSeparator_spec {ι : Type*} [Finite ι]
    (ν : Valuation K ℝ≥0) (hν : ν.IsNontrivial)
    (w : ι → Valuation Ω ℝ≥0) (hw : Function.Injective w)
    (hres : ∀ i, (w i).comap (algebraMap K Ω) = ν) (i : ι) :
    let x := normalizedRealProlongationSeparator ν hν w hw hres i
    w i x < 1 ∧ ∀ j, j ≠ i → w j (x - 1) < 1 :=
  (exists_normalizedRealProlongation_separator ν hν w hw hres i).choose_spec

end Langlands.FieldTheory
