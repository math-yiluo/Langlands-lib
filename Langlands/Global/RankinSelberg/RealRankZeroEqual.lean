import Langlands.LocalFactor.RealBlockRankOne
import Langlands.Global.RankinSelberg.RealRankZeroLocal
import Langlands.Global.RankinSelberg.RealRankZeroParameter

/-! # The equal-rank real-place functional equation for `GL₁ × GL₁`

The case `r = 0` of `RealEqualFunctionalEquationStatement`, from the real Tate statement
`RealArchimedeanTateStatement`. A real-place parameter of a realization of `GL₁` is a single
character block `[character c]`; its Schur scalars identify every archimedean restriction of
a global Whittaker function with a multiple of `χ_c ∘ det`; the contragredient parameters have
the same parities and negated exponents; and the local computation `realEqual_rankZero` then
gives all nine conclusions. The central sign `ω'_v(-1)^0` is `1`. See the paired Markdown.
-/

noncomputable section

universe u

open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.LocalFactor Langlands.Automorphic ArchimedeanLocal

attribute [local instance] unitsMeasurable unitsBorel rankZeroGLMeasurable rankZeroGLBorel
  rankZeroNMeasurable rankZeroNBorel rankZeroQMeasurable rankZeroQBorel

/-- **The equal-rank real-place functional equation for `GL₁ × GL₁`.** For cuspidal
realizations `T`, `T'` of `GL₁` with contragredients `Td`, `Td'`, real-place parameters
`d`, `d'`, `dd`, `dd'` at `v`, any `a ∈ ℝˣ`, quotient measure `D`, archimedean restrictions
`W`, `W'` of global Whittaker functions for `χ` and `χ⁻¹` (any additive character `χ`), and
Schwartz function `Φ` on `ℝ¹`, the nine conclusions of `RealEqualFunctionalEquationStatement`
at `r = 0` hold, assuming the real Tate statement. -/
theorem realEqual_rankZero_global (hTate : RealArchimedeanTateStatement)
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (χ : AddChar (Adeles F) ℂ) (T Td T' Td' : CuspidalOperatorRealization F 0)
    (hTd : OperatorRealization.IsContragredientOf Td.realization T.realization)
    (hTd' : OperatorRealization.IsContragredientOf Td'.realization T'.realization)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ) (d d' dd dd' : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d)
    (hd' : T'.realization.HasRealPlaceParameter v d')
    (hdd : Td.realization.HasRealPlaceParameter v dd)
    (hdd' : Td'.realization.HasRealPlaceParameter v dd')
    (D : RealQuotientMeasureData 0) (W W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (0 + 1) → ℝ) ℂ)
    (hW : IsRealPlaceWhittaker F T χ v W) (hW' : IsRealPlaceWhittaker F T' χ⁻¹ v W') :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
          (ArchimedeanLocal.dualFunction (0 + 1) W') (realFourierTransform a Φ) s)
          D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
      MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
      (∀ s : ℂ, σ < s.re → realEqualIntegral D W W' Φ s = M s) ∧
      (∀ s : ℂ, σ < s.re → realEqualDualIntegral a D W W' Φ s = Md s) ∧
      ∀ᶠ s in Filter.codiscrete ℂ,
        ((realPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
          realMinusOneScalar T' v ^ 0 *
            (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
            ((realPairLFactor dd dd').denominator (1 - s))⁻¹ * M s := by
  obtain ⟨c, rfl⟩ := eq_singleton_of_realRank_eq_one hd.1
  obtain ⟨c', rfl⟩ := eq_singleton_of_realRank_eq_one hd'.1
  obtain ⟨cd, rfl⟩ := eq_singleton_of_realRank_eq_one hdd.1
  obtain ⟨cd', rfl⟩ := eq_singleton_of_realRank_eq_one hdd'.1
  obtain ⟨C, hC⟩ := isRealPlaceWhittaker_rankZero hW c
    (hasRealPlaceParameter_compact T.realization T.irreducible v c hd)
    (hasRealPlaceParameter_lie T.realization T.irreducible v c hd)
  obtain ⟨C', hC'⟩ := isRealPlaceWhittaker_rankZero hW' c'
    (hasRealPlaceParameter_compact T'.realization T'.irreducible v c' hd')
    (hasRealPlaceParameter_lie T'.realization T'.irreducible v c' hd')
  have hpar : (cd.mul cd').parity = (c.mul c').parity := by
    change cd.parity + cd'.parity = c.parity + c'.parity
    rw [contragredient_parity_rankOne T.irreducible Td.irreducible hTd v c cd hd hdd,
      contragredient_parity_rankOne T'.irreducible Td'.irreducible hTd' v c' cd' hd' hdd']
  have hexp : (cd.mul cd').exponent = -(c.mul c').exponent := by
    change cd.exponent + cd'.exponent = -(c.exponent + c'.exponent)
    rw [contragredient_exponent_rankOne T.irreducible Td.irreducible hTd v c cd hd hdd,
      contragredient_exponent_rankOne T'.irreducible Td'.irreducible hTd' v c' cd' hd' hdd',
      neg_add]
  obtain ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    realEqual_rankZero hTate a c c' cd cd' hpar hexp D hC hC' Φ
  refine ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  filter_upwards [h9] with s hs
  rw [pow_zero, one_mul]
  exact hs

end Langlands.Global.RankinSelbergGlobal.RealRankZero
