import Langlands.Global.RankinSelberg.ArchimedeanDualNonvanishing
import Langlands.Global.RankinSelberg.LocallyCompactFieldQuotientMeasures
import Langlands.Global.RankinSelberg.RealRankZeroEqual
import Langlands.LocalFactor.Archimedean.RealTateProof
import Langlands.Automorphic.RankOneDeterminantBand

/-! # Equal-rank tests at a real place for `GL₁ × GL₁` -/

noncomputable section

universe u

open NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.Automorphic Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ContinuousRationalFunctions ArchimedeanLocal

attribute [local instance] unitsMeasurable unitsBorel rankZeroGLMeasurable rankZeroGLBorel
  rankZeroNMeasurable rankZeroNBorel rankZeroQMeasurable rankZeroQBorel

local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

section Actual

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Some vector in a `GL₁` realization has nonzero value at the identity. -/
theorem exists_evaluate_one_ne_zero (T : CuspidalOperatorRealization F 0) :
    ∃ x : T.Space, evaluate F 1 (T.realization.toContinuous x) 1 ≠ 0 := by
  obtain ⟨x, g, hg⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  have he := T.realization.centralCharacter_evaluate ω hω x (AdelicGL.determinant F 1 g) 1
  rw [mul_one, AdelicGL.scalar_determinant_one] at he
  refine ⟨x, fun hx => hg ?_⟩
  rw [he, hx, mul_zero]

omit [CompactSpace (AdeleQuotient F)] in
/-- The adelic point with both parts equal to the identity is the identity. -/
theorem adelicPoint_one_one : adelicPoint F 1 1 1 = 1 := by
  have h : AdelicGL.pair F 1 1 1 = 1 := by
    simpa only [map_one] using (AdelicGL.pair_projections F 1 (1 : AdelicGL F 1))
  simp [adelicPoint, h]

private theorem exists_actual_character
    (T : CuspidalOperatorRealization F 0) (χ : AddChar (Adeles F) ℂ)
    (v : {v : InfinitePlace F // v.IsReal}) (c : RealCharacterData)
    (hc : T.realization.HasRealPlaceParameter v [RealBlock.character c]) :
    ∃ (W : Langlands.GeneralLinear 1 ℝ → ℂ) (C : ℂ),
      IsRealPlaceWhittaker F T χ v W ∧ C ≠ 0 ∧
        ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ) := by
  obtain ⟨x, hx⟩ := exists_evaluate_one_ne_zero T
  let W (g : Langlands.GeneralLinear 1 ℝ) :=
    cuspWhittaker F T χ x (realPlacePoint F 1 v g * finitePoint F 1 1)
  have hW : IsRealPlaceWhittaker F T χ v W := ⟨x, 1, rfl⟩
  obtain ⟨C, hC⟩ := isRealPlaceWhittaker_rankZero hW c
    (hasRealPlaceParameter_compact T.realization T.irreducible v c hc)
    (hasRealPlaceParameter_lie T.realization T.irreducible v c hc)
  have hWone : W 1 = evaluate F 1 (T.realization.toContinuous x) 1 := by
    change cuspWhittaker F T χ x (realPlacePoint F 1 v 1 * finitePoint F 1 1) = _
    rw [cuspWhittaker_rankZero, RealPlaceWhittaker.cuspFunction_eq_evaluate]
    simp [realPlacePoint, finitePoint, adelicPoint_one_one]
  refine ⟨W, C, hW, fun hzero => hx ?_, hC⟩
  rw [← hWone, hC 1, hzero, zero_mul]

/-- For any compatible quotient measure, one real Gaussian test works for the ordinary
and dual integrals at rank one. -/
theorem realEqual_rankZero_tests
    (χ : AddChar (Adeles F) ℂ) (T Td T' Td' : CuspidalOperatorRealization F 0)
    (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
    (hTd' : OperatorRealization.IsContragredientOf Td'.realization T'.realization)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (d d' dd dd' : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d)
    (hd' : T'.realization.HasRealPlaceParameter v d')
    (hdd : Td.realization.HasRealPlaceParameter v dd)
    (hdd' : Td'.realization.HasRealPlaceParameter v dd') (D : RealQuotientMeasureData 0) :
    ∃ (W W' : Langlands.GeneralLinear 1 ℝ → ℂ) (Φ : SchwartzMap (Fin 1 → ℝ) ℂ),
      IsRealPlaceWhittaker F T χ v W ∧ IsRealPlaceWhittaker F T' χ⁻¹ v W' ∧
        HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) ∧
        HolomorphicNonzeroOnRightHalfPlane (realEqualDualIntegral a D W W' Φ) := by
  obtain ⟨c, rfl⟩ := eq_singleton_of_realRank_eq_one hd.1
  obtain ⟨c', rfl⟩ := eq_singleton_of_realRank_eq_one hd'.1
  obtain ⟨W, C, hW, hC0, hC⟩ := exists_actual_character T χ v c hd
  obtain ⟨W', C', hW', hC'0, hC'⟩ := exists_actual_character T' χ⁻¹ v c' hd'
  let e := (c.mul c').parity
  let t := (c.mul c').exponent
  let Φ : SchwartzMap (Fin 1 → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) (RealTate.gaussSchwartzE e)
  have hΦ : lineSchwartz Φ = RealTate.gaussSchwartzE e := by
    ext x
    rfl
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq (D := D)
  obtain ⟨σ, M, Md, _, _, hf, hg, hM, _, ho, hdu, he⟩ :=
    realEqual_rankZero_global RealTate.realArchimedeanTateStatement χ T Td T' Td'
      hTd hTd' v a _ _ dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
  let z : ℂ := ((max σ (-t.re) + 1 : ℝ) : ℂ)
  have hz : σ < z.re := by
    change σ < max σ (-t.re) + 1
    linarith [le_max_left σ (-t.re)]
  have hz' : 0 < (z + t).re := by
    change 0 < max σ (-t.re) + 1 + t.re
    linarith [le_max_right σ (-t.re)]
  have hn : HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) := by
    refine ⟨σ, hf, z, hz, ?_⟩
    rw [equalIntegral_eq c c' hκ hC hC' Φ, hΦ, RealTate.zeta_gaussSchwartzE e hz']
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
    exact mul_ne_zero hκ' (mul_ne_zero (mul_ne_zero hC0 hC'0)
      (Complex.Gammaℝ_ne_zero_of_re_pos (RealTate.re_add_pos hz' e)))
  refine ⟨W, W', Φ, hW, hW', hn, ?_⟩
  exact holomorphicNonzero_dual_of_functionalEquation σ (realPairLFactor dd dd')
    (realPairEpsilon [RealBlock.character c] [RealBlock.character c'] a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)))
    (realMinusOneScalar T' v ^ 0) (by simp) hn hf hg hM ho hdu he

/-- The quotient measure and both nonzero tests exist for real rank-one data. -/
theorem realEqual_rankZero_tests_exists
    (χ : AddChar (Adeles F) ℂ) (T Td T' Td' : CuspidalOperatorRealization F 0)
    (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
    (hTd' : OperatorRealization.IsContragredientOf Td'.realization T'.realization)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (d d' dd dd' : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d)
    (hd' : T'.realization.HasRealPlaceParameter v d')
    (hdd : Td.realization.HasRealPlaceParameter v dd)
    (hdd' : Td'.realization.HasRealPlaceParameter v dd') :
    ∃ (W W' : Langlands.GeneralLinear 1 ℝ → ℂ) (Φ : SchwartzMap (Fin 1 → ℝ) ℂ)
      (D : RealQuotientMeasureData 0),
      IsRealPlaceWhittaker F T χ v W ∧ IsRealPlaceWhittaker F T' χ⁻¹ v W' ∧
        HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) ∧
        HolomorphicNonzeroOnRightHalfPlane (realEqualDualIntegral a D W W' Φ) := by
  obtain ⟨D⟩ := quotientMeasureData_nonempty ℝ 0
  obtain ⟨W, W', Φ, hW, hW', ho, hdu⟩ :=
    realEqual_rankZero_tests χ T Td T' Td' hTd hTd' v a d d' dd dd' hd hd' hdd hdd' D
  exact ⟨W, W', Φ, D, hW, hW', ho, hdu⟩

end Actual

end Langlands.Global.RankinSelbergGlobal.RealRankZero
