import Langlands.Global.Factors.CuspidalPairPoleStatement

/-!
# Vertical-strip bounds of continued cuspidal pair L-functions

The vertical-strip clause of Getz–Hahn (2024), Theorem 11.7.1, and Cogdell (2004),
Theorem 4.1(2), separated from the continuation: a completed cuspidal pair L-function that
continues holomorphically to `ℂ ∖ {0, 1}` is bounded in vertical strips away from `0` and
`1`. Proposition definition only. See the paired Markdown for sources and the scope.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean
open CuspidalPairPoles

/-- **Getz–Hahn (2024), Theorem 11.7.1, and Cogdell (2004), Theorem 4.1(2)**: bounds in
vertical strips.

For actual cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)` over a number field,
both trivial on the split components of their centres, spectral presentations with
irreducible admissible finite components, a choice `c` of finite pair L-data and archimedean
parameters of both realizations: every completed L-function `Λ` (`c.IsCompletedLFunction`)
that is holomorphic on `ℂ ∖ {0, 1}` is bounded in vertical strips away from `0` and `1`. -/
def CuspidalPairVerticalStripStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
      (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
      (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    ∀ (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
      (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
      (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    let infiniteL (s : ℂ) : ℂ :=
      (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
    ∀ Λ : ℂ → ℂ, c.IsCompletedLFunction infiniteL Λ → DifferentiableOn ℂ Λ {0, 1}ᶜ →
      IsBoundedInVerticalStrips Λ

end Langlands.Global
