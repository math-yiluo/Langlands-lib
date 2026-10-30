import Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement
import Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof
import Langlands.HarmonicAnalysis.FiniteTranslationOrbitProof
import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Proof of the shell generating integrals of finite functions

This module proves `Langlands.RankinSelberg.FiniteFunctionShellSeriesStatement`.
The uniformizer is the one supplied by the valuation-shell decomposition, and the
recurrence and growth base are those of the translation orbit of the finite
function along that uniformizer. For a test function, the valuation cutoffs give
the lower support bound and constancy past the upper cutoff; integrating the orbit
recurrence over the integral units then gives the recurrent tail. The shell norm
integrals vanish below the lower cutoff and are dominated by a geometric series
with ratio `B * ‖z‖` on nonnegative shells, so the shell integrability criterion
and the shell-sum identity apply.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF

/-- Proof of `FiniteFunctionShellSeriesStatement`: one uniformizer, one recurrence
and one geometric base serve every Schwartz--Bruhat test function. -/
theorem finiteFunctionShellSeries : FiniteFunctionShellSeriesStatement.{uF} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  intro η hηc hηfin μ K
  -- The uniformizer and the shell decomposition.
  obtain ⟨π, hπ, hS0, -, -, hS, hcrit, hident⟩ := valuationShellIntegration p hp F T
  obtain ⟨-, -, hKc, hKm, hK1, -⟩ := hS 0
  rw [hS0] at hKc hKm hK1
  have hK0 : ∀ u ∈ K, T.ord (u : F.Carrier) = 0 := fun u hu =>
    (Set.ext_iff.mp hS0 u).mpr hu
  have hord (n : ℤ) (a : F.Carrierˣ) :
      T.ord ((π ^ n * a : F.Carrierˣ) : F.Carrier) = n + T.ord (a : F.Carrier) := by
    rw [Units.val_mul, T.ord_mul (π ^ n).ne_zero a.ne_zero, Units.val_zpow_eq_zpow_val,
      T.ord_zpow, hπ, mul_one]
  have hordK (n : ℤ) (u : F.Carrierˣ) (hu : u ∈ K) :
      T.ord ((π ^ n * u : F.Carrierˣ) : F.Carrier) = n := by
    rw [hord, hK0 u hu, add_zero]
  have hηK (m : ℤ) : IntegrableOn (fun u => η (π ^ m * u)) K μ :=
    (hηc.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact' hKc hKm
  -- The orbit recurrence and growth base along the uniformizer.
  obtain ⟨E, B, hB, hrec, hgrowth⟩ := finiteTranslationOrbit F.Carrierˣ η hηc hηfin π
  obtain ⟨C, hC, hCb⟩ := hgrowth K hKc
  refine ⟨π, E, B, hπ, hB, fun Φ => ?_⟩
  intro c
  obtain ⟨L, N, CΦ, hLN, hCΦ, hΦb, hΦlow, hΦhigh⟩ := schwartzBruhatValuationBounds p F T Φ
  -- Vanishing below the lower cutoff.
  have hlow : ∀ n : ℤ, n < L → c n = 0 := by
    intro n hn
    show ∫ u in K, Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) * η (π ^ n * u) ∂μ = 0
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    rw [hΦlow _ (by rw [hordK n u hu]; exact hn), zero_mul]
  -- Past the upper cutoff the coefficient is `Φ 0` times an orbit integral.
  have hhigh : ∀ n : ℤ, (N : ℤ) ≤ n → c n = Φ 0 * ∫ u in K, η (π ^ n * u) ∂μ := by
    intro n hn
    show ∫ u in K, Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) * η (π ^ n * u) ∂μ = _
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hKm fun u hu => ?_
    show Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) * η (π ^ n * u) = Φ 0 * η (π ^ n * u)
    rw [hΦhigh _ (by rw [hordK n u hu]; exact hn)]
  -- The recurrent tail.
  have hrecK : E.IsSolution (fun j : ℕ => c ((j : ℤ) + (N : ℤ))) := by
    intro j
    show c (((j + E.order : ℕ) : ℤ) + N) =
      ∑ i : Fin E.order, E.coeffs i * c (((j + i : ℕ) : ℤ) + N)
    have horbit : ∫ u in K, η (π ^ (((j + E.order : ℕ) : ℤ) + N) * u) ∂μ =
        ∑ i : Fin E.order, E.coeffs i * ∫ u in K, η (π ^ (((j + i : ℕ) : ℤ) + N) * u) ∂μ :=
      calc ∫ u in K, η (π ^ (((j + E.order : ℕ) : ℤ) + N) * u) ∂μ
          = ∫ u in K, ∑ i : Fin E.order,
              E.coeffs i * η (π ^ (((j + i : ℕ) : ℤ) + N) * u) ∂μ := by
            congr 1
            funext u
            exact hrec N u j
        _ = ∑ i : Fin E.order,
              ∫ u in K, E.coeffs i * η (π ^ (((j + i : ℕ) : ℤ) + N) * u) ∂μ :=
            integral_finsetSum _ fun i _ => (hηK _).const_mul _
        _ = _ := Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hhigh _ (by omega), horbit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hhigh _ (by omega), mul_left_comm]
  refine ⟨L, N, hLN, hlow, hrecK, fun z hz hBz => ?_⟩
  -- The weighted integrand and its shell integrals.
  let f : F.Carrierˣ → ℂ := fun a => Φ (a : F.Carrier) * η a * z ^ (T.ord (a : F.Carrier))
  have hfc : Continuous f :=
    ((Φ.continuous.comp Units.continuous_val).mul hηc).mul
      ((continuous_of_discreteTopology (f := fun m : ℤ => z ^ m)).comp
        (continuous_ord_units T))
  have hfK (n : ℤ) (u : F.Carrierˣ) (hu : u ∈ K) : f (π ^ n * u) =
      Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) * η (π ^ n * u) * z ^ n := by
    simp only [f, hordK n u hu]
  have hcoef (n : ℤ) : ∫ u in K, f (π ^ n * u) ∂μ = c n * z ^ n := by
    rw [setIntegral_congr_fun hKm fun u hu => hfK n u hu, integral_mul_const]
  have hnormK (n : ℤ) (u : F.Carrierˣ) (hu : u ∈ K) : ‖f (π ^ n * u)‖ =
      ‖Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier)‖ * ‖η (π ^ n * u)‖ * ‖z‖ ^ n := by
    rw [hfK n u hu, norm_mul, norm_mul, norm_zpow]
  -- Summability of the shell norm integrals.
  let h : ℤ → ℝ := fun n => ∫ u in K, ‖f (π ^ n * u)‖ ∂μ
  have hh0 (n : ℤ) : 0 ≤ h n := integral_nonneg fun u => norm_nonneg _
  have hhlow (n : ℤ) (hn : n < L) : h n = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    rw [hnormK n u hu, hΦlow _ (by rw [hordK n u hu]; exact hn), norm_zero, zero_mul,
      zero_mul]
  have hhpos (m : ℕ) : h m ≤ CΦ * C * (B * ‖z‖) ^ m := by
    have hbound : ∀ u ∈ K, ‖‖f (π ^ (m : ℤ) * u)‖‖ ≤ CΦ * C * (B * ‖z‖) ^ m := by
      intro u hu
      rw [norm_norm, hnormK m u hu, zpow_natCast]
      have h1 := hΦb ((π ^ (m : ℤ) * u : F.Carrierˣ) : F.Carrier)
      have h2 := hCb m u hu
      rw [Int.natAbs_natCast] at h2
      calc ‖Φ ((π ^ (m : ℤ) * u : F.Carrierˣ) : F.Carrier)‖ * ‖η (π ^ (m : ℤ) * u)‖ * ‖z‖ ^ m
          ≤ CΦ * (C * B ^ m) * ‖z‖ ^ m :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) hCΦ.le)
              (by positivity)
        _ = CΦ * C * (B * ‖z‖) ^ m := by ring
    have hK1' : μ.real K = 1 := by
      rw [Measure.real, show μ K = 1 from hK1, ENNReal.toReal_one]
    have := norm_setIntegral_le_of_norm_le_const (by rw [hK1]; exact ENNReal.one_lt_top) hbound
    rw [Real.norm_of_nonneg (hh0 m), hK1', mul_one] at this
    exact this
  have hBz0 : 0 ≤ B * ‖z‖ := mul_nonneg (by linarith) (norm_nonneg _)
  have hsumh : Summable h := by
    refine Summable.of_nat_of_neg ?_ ?_
    · exact Summable.of_nonneg_of_le (fun m => hh0 m) hhpos
        ((summable_geometric_of_lt_one hBz0 hBz).mul_left _)
    · refine summable_of_ne_finset_zero (s := Finset.range (L.natAbs + 1)) fun m hm => ?_
      rw [Finset.mem_range, not_lt] at hm
      exact hhlow _ (by omega)
  -- The shell integrability criterion and the shell-sum identity.
  have hint : Integrable f μ := (hcrit f hfc).2.2 hsumh
  obtain ⟨hsum, heq⟩ := hident f hfc hint
  exact ⟨hint, (summable_congr hcoef).mp hsum, heq.trans (tsum_congr hcoef)⟩

end Langlands.RankinSelberg
