import Langlands.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
import Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroIntegralLaws
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Spectral expansion of the actual adjacent-rank finite coefficient formula. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration
open scoped BigOperators

/-- The finite interval form of the absolutely convergent integer Cauchy product.
The support bounds justify each finite sum, including empty intervals. -/
theorem hasSum_intervalConvolution
    (a b : ℤ → ℂ) (La Lb : ℤ)
    (ha0 : ∀ k, k < La → a k = 0) (hb0 : ∀ k, k < Lb → b k = 0)
    (z A B : ℂ) (hz : z ≠ 0)
    (ha : HasSum (fun k => a k * z ^ k) A)
    (hb : HasSum (fun k => b k * z ^ k) B) :
    Summable (fun m : ℤ => ‖(∑ k ∈ Finset.Icc La (m - Lb), a k * b (m - k)) * z ^ m‖) ∧
      HasSum (fun m : ℤ => (∑ k ∈ Finset.Icc La (m - Lb), a k * b (m - k)) * z ^ m)
        (A * B) := by
  classical
  let f := fun k : ℤ => a k * z ^ k
  let g := fun k : ℤ => b k * z ^ k
  have hfn : Summable (fun k => ‖f k‖) := summable_norm_iff.mpr ha.summable
  have hgn : Summable (fun k => ‖g k‖) := summable_norm_iff.mpr hb.summable
  have hp : HasSum (fun x : ℤ × ℤ => f x.1 * g x.2) (A * B) := by
    rw [← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_of_summable_norm hfn hgn]
    exact (summable_mul_of_summable_norm hfn hgn).hasSum
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun x => (x.2, x.1 - x.2)
      invFun := fun x => (x.1 + x.2, x.1)
      left_inv := fun x => by
        apply Prod.ext
        · dsimp; omega
        · rfl
      right_inv := fun x => by
        apply Prod.ext
        · rfl
        · dsimp; omega }
  have hre := e.hasSum_iff.mpr hp
  have hs : HasSum
      (fun m : ℤ => (∑ k ∈ Finset.Icc La (m - Lb), a k * b (m - k)) * z ^ m)
      (A * B) := by
    apply hre.prod_fiberwise
    intro m
    have hzero : ∀ k ∉ Finset.Icc La (m - Lb), f k * g (m - k) = 0 := by
      intro k hk
      dsimp only [f, g]
      by_cases hka : k < La
      · rw [ha0 k hka, zero_mul, zero_mul]
      · have hkb : m - k < Lb := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hk
          omega
        rw [hb0 (m - k) hkb, zero_mul, mul_zero]
    have hfin : HasSum (fun k : ℤ => f k * g (m - k))
        (∑ k ∈ Finset.Icc La (m - Lb), f k * g (m - k)) :=
      hasSum_sum_of_ne_finset_zero hzero
    have heq : (∑ k ∈ Finset.Icc La (m - Lb), f k * g (m - k)) =
        (∑ k ∈ Finset.Icc La (m - Lb), a k * b (m - k)) * z ^ m := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [f, g]
      calc
        _ = (a k * b (m - k)) * (z ^ k * z ^ (m - k)) := by ring
        _ = _ := by rw [← zpow_add₀ hz, add_sub_cancel]
    simpa only [e, Equiv.coe_fn_mk, Function.comp_apply, heq] using hfin
  exact ⟨summable_norm_iff.mpr hs.summable, hs⟩

universe uF uV uW

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance spectralFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance spectralFieldValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance spectralLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance spectralFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance spectralGroupMeasurableSpace (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance spectralGroupBorelSpace (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance spectralQuotientMeasurableSpace (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance spectralQuotientBorelSpace (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- The group determinant coefficient in the actual finite model formula. -/
def adjacentRankMatrixSliceCoefficient {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ) : ℂ :=
  ∫ h, adjacentRankInnerSliceWeight F Φ χ m ((r : ℂ) / 2) h * f h
    ∂generalLinearHaar F.Carrier r

/-- The actual general-linear determinant fibers partition every convergent
matrix integral. -/
theorem hasSum_setIntegral_generalLinearDeterminantSlice {r : ℕ}
    (η : Measure (Langlands.GeneralLinear (r + 1) F.Carrier))
    {f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ}
    (hf : Integrable f η) :
    HasSum (fun m : ℤ => ∫ h in generalLinearDeterminantSlice
      F.canonicalTopologicalData r m, f h ∂η) (∫ h, f h ∂η) := by
  have hcover : (⋃ m : ℤ, generalLinearDeterminantSlice
      F.canonicalTopologicalData r m) = Set.univ := by
    ext h
    simp only [Set.mem_iUnion, mem_generalLinearDeterminantSlice, Set.mem_univ,
      iff_true]
    exact ⟨_, rfl⟩
  have hdisj : Pairwise (fun i j => Disjoint
      (generalLinearDeterminantSlice F.canonicalTopologicalData r i)
      (generalLinearDeterminantSlice F.canonicalTopologicalData r j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro h hi hj
    exact hij (hi.symm.trans hj)
  have h := hasSum_integral_iUnion
    (fun m => (isClopen_generalLinearDeterminantSlice
      F.canonicalTopologicalData r m).isClosed.measurableSet)
    hdisj (by rw [hcover]; exact hf.integrableOn)
  rwa [hcover, Measure.restrict_univ] at h

/-- The actual shifted matrix integral has the same spectral convention as the
quotient integrals, with base exponent `r/2`. -/
theorem setIntegral_matrixIntegrand_determinantSlice {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ) (s : ℂ) :
    (∫ h in generalLinearDeterminantSlice F.canonicalTopologicalData r m,
      GodementJacquet.matrixIntegrand abv Φ (s + (r : ℂ) / 2)
        (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g) h
          ∂generalLinearHaar F.Carrier r) =
      adjacentRankMatrixSliceCoefficient F Φ χ f m * spectralPoint qF s ^ m := by
  let S := generalLinearDeterminantSlice F.canonicalTopologicalData r m
  have hS : MeasurableSet S :=
    (isClopen_generalLinearDeterminantSlice F.canonicalTopologicalData r m).isClosed.measurableSet
  have heq : ∀ h ∈ S,
      GodementJacquet.matrixIntegrand abv Φ (s + (r : ℂ) / 2)
        (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g) h =
      (Φ h.val * (χ (GeneralLinear.determinant h) : ℂ) *
        determinantWeight abv h ((r : ℂ) / 2) * f h) * spectralPoint qF s ^ m := by
    intro h hh
    have hw : determinantWeight abv h s = spectralPoint qF s ^ m := by
      rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
      change F.canonicalTopologicalData.ord (Matrix.det h.val) = m at hh
      rw [hh]
    dsimp only [GodementJacquet.matrixIntegrand]
    rw [determinantWeight_exponent_add, hw]
    ring
  rw [setIntegral_congr_fun hS heq, integral_mul_const]
  congr 1
  rw [adjacentRankMatrixSliceCoefficient, ← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with h
  by_cases hh : h ∈ generalLinearDeterminantSlice F.canonicalTopologicalData r m
  · simp only [S, adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_mem hh]
  · simp only [S, adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_notMem hh, zero_mul]

/-- At each supplied convergent parameter the shifted matrix integral is the
absolutely summable series of the actual group coefficients. -/
theorem adjacentRankMatrixSliceExpansion {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (s : ℂ)
    (hs : GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
      (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g)) :
    Summable (fun m : ℤ => ‖adjacentRankMatrixSliceCoefficient F Φ χ f m *
      spectralPoint qF s ^ m‖) ∧
      HasSum (fun m : ℤ => adjacentRankMatrixSliceCoefficient F Φ χ f m *
        spectralPoint qF s ^ m)
        (GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
          (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g)) := by
  have h := hasSum_setIntegral_generalLinearDeterminantSlice F
    (generalLinearHaar F.Carrier r) hs
  simp only [setIntegral_matrixIntegrand_determinantSlice F Φ χ f] at h
  exact ⟨summable_norm_iff.mpr h.summable, h⟩

/-- The actual corank-one integrand has the standard spectral weight on each
quotient determinant slice. -/
theorem corankOneIntegrand_eq_mul_spectralPoint_zpow {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (m : ℤ) (q : LeftUnipotentQuotient r F.Carrier)
    (hq : q ∈ determinantSlice F.canonicalTopologicalData r m) (s : ℂ) :
    corankOneIntegrand ψ abv U W' s q =
      corankOneIntegrand ψ abv U W' 0 q * spectralPoint qF s ^ m := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hq
    rw [corankOneIntegrand_mk, corankOneIntegrand_mk]
    have hexp : s - 1 / 2 = (0 - 1 / 2) + s := by ring
    have hw : determinantWeight abv g s = spectralPoint qF s ^ m := by
      rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
      change F.canonicalTopologicalData.ord (Matrix.det g.val) = m at hq
      rw [hq]
    rw [hexp, determinantWeight_exponent_add, hw]
    ring

/-- At every convergent parameter the actual corank-one integral is the
absolutely summable series of its coefficients at zero. -/
theorem corankOneSliceExpansion {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier)) (s : ℂ)
    (hs : Integrable (corankOneIntegrand ψ abv U W' s) ν) :
    Summable (fun m : ℤ => ‖sliceCoefficient F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m‖) ∧
      HasSum (fun m : ℤ => sliceCoefficient F.canonicalTopologicalData ν
        (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m)
        (∫ q, corankOneIntegrand ψ abv U W' s q ∂ν) := by
  have heq : ∀ m : ℤ,
      (∫ q in determinantSlice F.canonicalTopologicalData r m,
        corankOneIntegrand ψ abv U W' s q ∂ν) =
      sliceCoefficient F.canonicalTopologicalData ν
        (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m := by
    intro m
    rw [setIntegral_congr_fun
      (measurableSet_determinantSlice F.canonicalTopologicalData r m)
      (fun q hq => corankOneIntegrand_eq_mul_spectralPoint_zpow F ψ U W' m q hq s),
      integral_mul_const]
    rfl
  exact ⟨by simpa only [heq] using
      summable_norm_setIntegral_determinantSlice F.canonicalTopologicalData ν hs,
    by simpa only [heq] using
      hasSum_setIntegral_determinantSlice F.canonicalTopologicalData ν hs⟩

end Padic
end Langlands.RankinSelberg
