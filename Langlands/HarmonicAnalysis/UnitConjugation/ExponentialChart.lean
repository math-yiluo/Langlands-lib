import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # Exponential coordinates over a characteristic-zero ultrametric field -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Function Set _root_.Topology
open scoped ENNReal NNReal

variable (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F]

private theorem exists_norm_factorial_bound : ∃ r : ℝ≥0, 0 < r ∧
    ∀ n : ℕ, (r : ℝ) ^ n ≤ ‖(n.factorial : F)‖ := by
  let v := NormedField.valuation (K := F)
  let O := v.valuationSubring
  let k := IsLocalRing.ResidueField O
  let p := ringChar k
  have hchar : ∀ n : ℕ, p ∣ n ↔ ‖(n : F)‖ < 1 := by
    intro n
    rw [← CharP.cast_eq_zero_iff k p, ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    change ‖O.subtype (n : O)‖₊ < 1 ↔ _
    rw [map_natCast O.subtype n, ← NNReal.coe_lt_coe, NNReal.coe_one]
    rfl
  have hprime := CharP.char_is_prime_or_zero k p
  rcases hprime with hp | hp
  · let : Fact p.Prime := ⟨hp⟩
    have hp₀ : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hpn : 0 < ‖(p : F)‖₊ := nnnorm_pos.mpr hp₀
    refine ⟨‖(p : F)‖₊, hpn, fun n => ?_⟩
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd n.factorial_ne_zero p hp.ne_one
    have hm₀ : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
    have hn : ‖(m : F)‖ = 1 := le_antisymm (IsUltrametricDist.norm_natCast_le_one F m)
      (not_lt.mp (fun h => hm ((hchar m).2 h)))
    have hen : e ≤ n := by
      have h := padicValNat_factorial_le p n
      rw [he, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm₀, padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hm, add_zero] at h
      exact h
    rw [he, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hn, mul_one]
    exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one F p) hen
  · refine ⟨1, zero_lt_one, fun n => ?_⟩
    simp only [NNReal.coe_one, one_pow]
    apply not_lt.mp
    intro h
    exact n.factorial_ne_zero (by simpa only [hp, zero_dvd_iff] using (hchar n.factorial).2 h)

variable (A : Type*) [NormedRing A] [NormedAlgebra F A]

/-- The exponential power series has positive radius in characteristic zero over an
ultrametric field, with no restriction on its residue characteristic. -/
def ExponentialPositiveRadiusStatement : Prop := 0 < (NormedSpace.expSeries F A).radius

theorem exponentialPositiveRadius : ExponentialPositiveRadiusStatement F A := by
  obtain ⟨r, hr, hb⟩ := exists_norm_factorial_bound F
  have hbound (n : ℕ) : ‖NormedSpace.expSeries F A n‖ * (r : ℝ) ^ n ≤ max (1 : ℝ) ‖(1 : A)‖ := by
    let C := max (1 : ℝ) ‖(1 : A)‖
    have hn : 0 < ‖(n.factorial : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    calc
      _ ≤ ‖(n.factorial : F)‖⁻¹ * C * (r : ℝ) ^ n := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [NormedSpace.expSeries, ← norm_inv]
        let m := ContinuousMultilinearMap.mkPiAlgebraFin F n A
        have hm : ‖m‖ ≤ C := ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
        exact (m.opNorm_smul_le ((n.factorial : F)⁻¹)).trans
          (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
      _ = (r : ℝ) ^ n / ‖(n.factorial : F)‖ * C := by ring
      _ ≤ _ := by
        have h := (div_le_one₀ hn).mpr (hb n)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right h (le_trans zero_le_one (le_max_left _ _))
  exact (show (0 : ℝ≥0∞) < (r : ℝ≥0∞) by exact_mod_cast hr).trans_le
    ((NormedSpace.expSeries F A).le_radius_of_bound _ hbound)

variable {F A}

omit [IsUltrametricDist F] in
/-- Continuous algebra automorphisms commute with the exponential, since a continuous
linear equivalence commutes with the sum of the exponential series. -/
theorem map_exp_sub_one [CompleteSpace F] [FiniteDimensional F A] (e : A ≃ₐ[F] A) (x : A) :
    e (NormedSpace.exp x - 1) = NormedSpace.exp (e x) - 1 := by
  let E := e.toLinearEquiv.toContinuousLinearEquiv
  rw [map_sub, map_one]
  congr 1
  have h := congrFun (NormedSpace.exp_eq_tsum F (𝔸 := A)) x
  have h' := congrFun (NormedSpace.exp_eq_tsum F (𝔸 := A)) (e x)
  rw [h, h']
  change E (∑' n : ℕ, ((n.factorial : F)⁻¹) • x ^ n) = _
  rw [E.map_tsum]
  exact tsum_congr (fun n => by
    change e (((n.factorial : F)⁻¹) • x ^ n) = _
    rw [map_smul, map_pow])

variable [CompleteSpace A]

/-- Exponential coordinates `X ↦ exp(X) - 1` around zero can be restricted to have
image in any prescribed open neighborhood of zero. -/
def ExponentialChartStatement : Prop :=
  ∀ W : Set A, IsOpen W → 0 ∈ W → ∃ e : OpenPartialHomeomorph A A,
    0 ∈ e.source ∧ 0 ∈ e.target ∧ e.target ⊆ W ∧
    e.source ⊆ Metric.eball 0 (NormedSpace.expSeries F A).radius ∧
    ∀ x : A, e x = NormedSpace.exp x - 1

theorem exponentialChart : ExponentialChartStatement (F := F) (A := A) := by
  intro W hW hW₀
  have hr := exponentialPositiveRadius F A
  let l : A ≃L[F] A := ContinuousLinearEquiv.refl F A
  let f (x : A) := NormedSpace.exp x - 1
  have hd : HasStrictFDerivAt f (l : A →L[F] A) 0 :=
    (hasStrictFDerivAt_exp_zero_of_radius_pos hr).sub_const 1
  have hf₀ : f 0 = 0 := by simp [f]
  let e₀ := hd.toOpenPartialHomeomorph f
  let V := e₀.source ∩ e₀ ⁻¹' W ∩ Metric.eball 0 (NormedSpace.expSeries F A).radius
  have hV : IsOpen V := (e₀.isOpen_inter_preimage hW).inter Metric.isOpen_eball
  let e := e₀.restrOpen V hV
  have h₀ : 0 ∈ e₀.source := hd.mem_toOpenPartialHomeomorph_source
  have he₀ : e₀ 0 = 0 := hf₀
  have hpre : 0 ∈ e₀ ⁻¹' W := by change e₀ 0 ∈ W; rwa [he₀]
  have hsrc : 0 ∈ e.source :=
    ⟨h₀, ⟨h₀, hpre⟩, Metric.mem_eball_self hr⟩
  have htar : 0 ∈ e.target := he₀ ▸ e.map_source hsrc
  refine ⟨e, hsrc, htar, ?_, fun _ hx => hx.2.2, fun _ => rfl⟩
  intro y hy
  have hx := e.map_target hy
  have hmem : e (e.symm y) ∈ W := hx.2.1.2
  rwa [e.right_inv hy] at hmem

end Langlands.HarmonicAnalysis.UnitConjugation
