import Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroIntegralLaws
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Determinant coefficients of the actual unequal-rank integral

Internal consequences of the published unequal-rank integrand, normalized
determinant weight and quotient determinant-slice partition. The expansion
requires genuine integrability and asserts no support or continuation result.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {n : ℕ} (j k : ℕ)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
  borel (LeftUnipotentQuotient n F.Carrier)
local instance : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier) :=
  borel (Matrix (Fin j) (Fin (n + 1)) F.Carrier)
local instance : BorelSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))
  (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
  (W : WhittakerFunctions ψ (n + (j + k + 1)))
  (W' : InverseWhittakerFunctions ψ n)

/-- Integrate the actual rectangular variable first, with its supplied measure. -/
def unequalRankAverage (s : ℂ) (q : LeftUnipotentQuotient n F.Carrier) : ℂ :=
  ∫ x, unequalRankIntegrand ψ abv j k W W' s x q ∂ν

/-- Actual unequal-rank coefficient series, with the rank-normalizing weight
already included by evaluating the integrand at the spectral parameter zero. -/
def unequalRankSliceCoefficient (m : ℤ) : ℂ :=
  sliceCoefficient F.canonicalTopologicalData μ (unequalRankAverage F j k ψ ν W W' 0) m

/-- The spectral factor depends only on the determinant slice and is independent
of the rectangular variable. -/
theorem unequalRankIntegrand_eq_mul_spectralPoint_zpow
    (m : ℤ) (q : LeftUnipotentQuotient n F.Carrier)
    (hq : q ∈ determinantSlice F.canonicalTopologicalData n m) (s : ℂ)
    (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier) :
    unequalRankIntegrand ψ abv j k W W' s x q =
      unequalRankIntegrand ψ abv j k W W' 0 x q *
        spectralPoint qF s ^ m := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hq
    rw [unequalRankIntegrand_mk, unequalRankIntegrand_mk]
    have hexp : s - ((j + k + 1 : ℕ) : ℂ) / 2 =
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2) + s := by ring
    have hw : determinantWeight abv g s = spectralPoint qF s ^ m := by
      rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
      change F.canonicalTopologicalData.ord (Matrix.det g.val) = m at hq
      rw [hq]
    rw [hexp, determinantWeight_exponent_add, hw]
    ring

/-- Rectangle integration retains the same exact slice spectral factor, even for
totalized integrals outside integrability. -/
theorem unequalRankAverage_eq_mul_spectralPoint_zpow
    (m : ℤ) (q : LeftUnipotentQuotient n F.Carrier)
    (hq : q ∈ determinantSlice F.canonicalTopologicalData n m) (s : ℂ) :
    unequalRankAverage F j k ψ ν W W' s q =
      unequalRankAverage F j k ψ ν W W' 0 q * spectralPoint qF s ^ m := by
  unfold unequalRankAverage
  simp_rw [unequalRankIntegrand_eq_mul_spectralPoint_zpow F j k ψ W W' m q hq s]
  rw [integral_mul_const]

/-- The actual restricted iterated integral is its coefficient at zero times the
spectral factor. No Fubini exchange or convergence assertion is involved. -/
theorem setIntegral_unequalRankAverage_determinantSlice (m : ℤ) (s : ℂ) :
    (∫ q in determinantSlice F.canonicalTopologicalData n m,
      unequalRankAverage F j k ψ ν W W' s q ∂μ) =
      unequalRankSliceCoefficient F j k ψ μ ν W W' m * spectralPoint qF s ^ m := by
  rw [setIntegral_congr_fun (measurableSet_determinantSlice F.canonicalTopologicalData n m)
    (fun q hq => unequalRankAverage_eq_mul_spectralPoint_zpow
      F j k ψ ν W W' m q hq s),
    integral_mul_const]
  rfl

/-- Genuine integrability of the rectangle average on a determinant slice is
independent of the spectral parameter. -/
theorem sliceIntegrableAt_unequalRankAverage_iff (m : ℤ) (s : ℂ) :
    SliceIntegrableAt F.canonicalTopologicalData μ (unequalRankAverage F j k ψ ν W W' s) m ↔
      SliceIntegrableAt F.canonicalTopologicalData μ (unequalRankAverage F j k ψ ν W W' 0) m := by
  have hq : (qF : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one).ne'
  have hc : spectralPoint qF s ^ m ≠ 0 := by
    apply zpow_ne_zero
    intro h
    exact hq ((Complex.cpow_eq_zero_iff _ _).mp h).1
  rw [sliceIntegrableAt_iff, sliceIntegrableAt_iff,
    integrableOn_congr_fun
      (fun q hq => unequalRankAverage_eq_mul_spectralPoint_zpow
        F j k ψ ν W W' m q hq s)
      (measurableSet_determinantSlice F.canonicalTopologicalData n m)]
  exact integrable_mul_const_iff (IsUnit.mk0 _ hc) _

/-- At a genuinely integrable parameter the iterated unequal-rank integral is the
absolutely summable series of its actual determinant coefficients. -/
theorem unequalRankSliceExpansion (s : ℂ)
    (hs : Integrable (unequalRankAverage F j k ψ ν W W' s) μ) :
    SliceIntegrable F.canonicalTopologicalData μ (unequalRankAverage F j k ψ ν W W' 0) ∧
      Summable (fun m : ℤ =>
        ‖unequalRankSliceCoefficient F j k ψ μ ν W W' m * spectralPoint qF s ^ m‖) ∧
      HasSum (fun m : ℤ =>
        unequalRankSliceCoefficient F j k ψ μ ν W W' m * spectralPoint qF s ^ m)
        (unequalRankIntegral ψ abv j k μ ν W W' s) := by
  have heq := setIntegral_unequalRankAverage_determinantSlice F j k ψ μ ν W W'
  refine ⟨fun m => (sliceIntegrableAt_unequalRankAverage_iff
    F j k ψ μ ν W W' m s).mp (sliceIntegrable_of_integrable (T := F.canonicalTopologicalData) hs m), ?_, ?_⟩
  · simpa only [heq] using summable_norm_setIntegral_determinantSlice F.canonicalTopologicalData μ hs
  · have h := hasSum_setIntegral_determinantSlice F.canonicalTopologicalData μ hs
    simp only [heq] at h
    exact h

/-- Actual product-space absolute convergence supplies the averaged integrability
needed for the coefficient expansion. Only the inner measure needs `SFinite`. -/
theorem unequalRankSliceExpansion_of_converges [SFinite ν] (s : ℂ)
    (hs : UnequalRankConverges ψ abv j k μ ν W W' s) :
    SliceIntegrable F.canonicalTopologicalData μ (unequalRankAverage F j k ψ ν W W' 0) ∧
      Summable (fun m : ℤ =>
        ‖unequalRankSliceCoefficient F j k ψ μ ν W W' m * spectralPoint qF s ^ m‖) ∧
      HasSum (fun m : ℤ =>
        unequalRankSliceCoefficient F j k ψ μ ν W W' m * spectralPoint qF s ^ m)
        (unequalRankIntegral ψ abv j k μ ν W W' s) := by
  exact unequalRankSliceExpansion F j k ψ μ ν W W' s hs.integral_prod_left

end Langlands.RankinSelberg
