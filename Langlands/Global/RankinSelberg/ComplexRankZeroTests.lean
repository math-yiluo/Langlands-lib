import Langlands.Global.RankinSelberg.RealRankZeroTests
import Langlands.Global.RankinSelberg.ComplexRankZeroLocal
import Langlands.Global.RankinSelberg.ComplexRankZeroWhittaker
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof

/-! # Equal-rank tests at a complex place for `GL₁ × GL₁` -/

noncomputable section

universe u

open NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Global.RankinSelbergGlobal.ComplexRankZero

open Langlands.Automorphic Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ContinuousRationalFunctions ArchimedeanLocal
open Langlands.Global.HeckeFunctionalEquation

attribute [local instance] unitsMeasurable unitsBorel rankZeroGLMeasurable rankZeroGLBorel
  rankZeroNMeasurable rankZeroNBorel rankZeroQMeasurable rankZeroQBorel

private local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

private theorem exists_actual_ne_zero_at_one
    (T : CuspidalOperatorRealization F 0) (χ : AddChar (Adeles F) ℂ)
    (w : {v : InfinitePlace F // v.IsComplex}) :
    ∃ W : Langlands.GeneralLinear 1 ℂ → ℂ, IsComplexPlaceWhittaker F T χ w W ∧ W 1 ≠ 0 := by
  obtain ⟨x, hx⟩ := RealRankZero.exists_evaluate_one_ne_zero T
  let W (g : Langlands.GeneralLinear 1 ℂ) :=
    cuspWhittaker F T χ x (complexPlacePoint F 1 w g * finitePoint F 1 1)
  refine ⟨W, ⟨x, 1, rfl⟩, ?_⟩
  change cuspWhittaker F T χ x (complexPlacePoint F 1 w 1 * finitePoint F 1 1) ≠ 0
  rw [RealRankZero.cuspWhittaker_rankZero, RealPlaceWhittaker.cuspFunction_eq_evaluate]
  simpa [complexPlacePoint, finitePoint, RealRankZero.adelicPoint_one_one] using hx

private def gaussian (m : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ m then starRingEnd ℂ z ^ m.natAbs else z ^ m.natAbs) *
      Complex.exp (-2 * (Real.pi : ℂ) * (‖z‖ : ℂ) ^ 2) / (Real.pi : ℂ)

/-- For any compatible quotient measure, the angular Gaussian gives nonzero ordinary
and dual tests for actual complex rank-one data, using complex Tate theory. -/
theorem complexEqual_rankZero_tests (hTate : ComplexArchimedeanTateStatement)
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (T T' : CuspidalOperatorRealization F 0)
    (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a)
    (d d' : List ComplexCharacterData)
    (hd : T.realization.HasComplexPlaceParameter w d)
    (hd' : T'.realization.HasComplexPlaceParameter w d') (D : ComplexQuotientMeasureData 0) :
    ∃ (W W' : Langlands.GeneralLinear 1 ℂ → ℂ) (Φ : SchwartzMap (Fin 1 → ℂ) ℂ),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
        HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) ∧
        HolomorphicNonzeroOnRightHalfPlane (complexEqualDualIntegral a D W W' Φ) := by
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd.1
  obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp hd'.1
  obtain ⟨W, hW, hW0⟩ := exists_actual_ne_zero_at_one T ψ.complex w
  obtain ⟨W', hW', hW'0⟩ := exists_actual_ne_zero_at_one T' ψ.complex⁻¹ w
  have hmodel := complexPlaceWhittakerModelReduction
    (complexPlaceWhittakerIntertwinerReduction complexPlaceWhittakerAnalytic)
  obtain ⟨C, hC⟩ := exists_eq_of_mem_complexWhittakerModel
    ((hmodel F ψ hψ 0 T w a ha [c] hd W).1 hW)
  obtain ⟨C', hC'⟩ := exists_eq_of_mem_complexWhittakerModel
    ((hmodel F ψ hψ 0 T' w a ha [c'] hd' W').2 hW')
  have hC0 : C ≠ 0 := fun hzero => hW0 (by rw [hC 1, hzero, zero_mul])
  have hC'0 : C' ≠ 0 := fun hzero => hW'0 (by rw [hC' 1, hzero, zero_mul])
  let m := (c.mul c').weight
  let t := (c.mul c').exponent
  obtain ⟨⟨f, hgauss⟩, _, hGauss⟩ := hTate.2.2.2 m
  have hfd : (f : ℂ → ℂ) = gaussian m := funext hgauss
  let Φ : SchwartzMap (Fin 1 → ℂ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ) f
  have hΦ : lineSchwartz Φ = f := by
    ext z
    rfl
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq D
  obtain ⟨σ, M, Md, _, _, hf, hg, hM, _, ho, hdu, he⟩ :=
    complexEqual_rankZero hTate a c c' D hC hC' Φ
  let z : ℂ := ((max σ (-t.re) + 1 : ℝ) : ℂ)
  have hz : σ < z.re := by
    change σ < max σ (-t.re) + 1
    linarith [le_max_left σ (-t.re)]
  have hz' : 0 < (z + t).re := by
    change 0 < max σ (-t.re) + 1 + t.re
    linarith [le_max_right σ (-t.re)]
  have hZ : ComplexTate.zeta (gaussian m) m t z =
      Complex.Gammaℂ (z + t + (m.natAbs : ℂ) / 2) := hGauss t z hz'
  have hΓ : Complex.Gammaℂ (z + t + (m.natAbs : ℂ) / 2) ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos ?_)
    · exact Complex.cpow_ne_zero_iff.mpr
        (.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · rw [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
      positivity
  have hn : HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) := by
    refine ⟨σ, hf, z, hz, ?_⟩
    rw [equalIntegral_eq c c' hκ hC hC' Φ, hΦ, hfd, hZ]
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
    exact mul_ne_zero (mul_ne_zero (div_ne_zero hκ' two_ne_zero) (mul_ne_zero hC0 hC'0)) hΓ
  refine ⟨W, W', Φ, hW, hW', hn, ?_⟩
  exact holomorphicNonzero_dual_of_functionalEquation σ
    (complexPairLFactor [c.inv] [c'.inv])
    (complexPairEpsilon [c] [c'] a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero))
    (complexCentralSign [c'] ^ 0) (by simp) hn hf hg hM ho hdu he

/-- The quotient measure and both nonzero tests exist for complex rank-one data
under the complex Tate theorem. -/
theorem complexEqual_rankZero_tests_exists (hTate : ComplexArchimedeanTateStatement)
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (T T' : CuspidalOperatorRealization F 0)
    (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a)
    (d d' : List ComplexCharacterData)
    (hd : T.realization.HasComplexPlaceParameter w d)
    (hd' : T'.realization.HasComplexPlaceParameter w d') :
    ∃ (W W' : Langlands.GeneralLinear 1 ℂ → ℂ) (Φ : SchwartzMap (Fin 1 → ℂ) ℂ)
      (D : ComplexQuotientMeasureData 0),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
        HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) ∧
        HolomorphicNonzeroOnRightHalfPlane (complexEqualDualIntegral a D W W' Φ) := by
  obtain ⟨D⟩ := quotientMeasureData_nonempty ℂ 0
  obtain ⟨W, W', Φ, hW, hW', ho, hdu⟩ :=
    complexEqual_rankZero_tests hTate ψ hψ T T' w a ha d d' hd hd' D
  exact ⟨W, W', Φ, D, hW, hW', ho, hdu⟩

end Langlands.Global.RankinSelbergGlobal.ComplexRankZero
