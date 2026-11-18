import Langlands.Automorphic.ComplexPlaceParameterWeights
import Langlands.Automorphic.ComplexPlaceParameterWeightsExamples
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement

/-!
# The totally complex archimedean bridge for cuspidal complex-place parameters

Three proposition definitions, over totally complex number fields, making explicit the
comparison between the complex-place standard-module parameters of an actual cuspidal
realization of `GL_(r+1)` and its infinitesimal character, after Clozel (1990),
Définitions 1.8 and 3.12 and the proof of Théorème 3.13:

* `CuspidalComplexParameterInfinitesimalCharacterTCStatement`: a full family of actual
  complex-place parameters of an actual cuspidal realization determines a unique matching
  character of the actual enveloping center, and every matching character acts by scalars on
  the realization;
* `ComplexParameterRegularAlgebraicTCStatement`: for a character of the enveloping center
  matching a family of complex-character lists, regular algebraicity in the sense of
  `ArchimedeanGL.IsRegularAlgebraicCharacter` is equivalent to Clozel regularity of every list;
* `CuspidalComplexParameterBridgeTCStatement`: the conjunction of the existing totally complex
  parameter-existence statement and the two statements above.

Proposition definitions only; nothing here is proved. The matching formulation is an internal
interface; see the paired Markdown for its provenance and use.
-/

noncomputable section

universe uF

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

/-- Over a totally complex number field, a full family `ds` of actual complex-place standard-module
parameters of an actual cuspidal realization `S` of `GL_(r+1)` determines a unique character
`χ` of the actual center of the enveloping algebra matching `ds`
(`ComplexPlaceParameter.MatchesInfinitesimalCharacter`), and every character matching `ds`
acts on `S` by scalars. -/
def CuspidalComplexParameterInfinitesimalCharacterTCStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)] (r : ℕ) (S : CuspidalOperatorRealization F r)
    (ds : {v : NumberField.InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter S.realization v (ds v)) →
      (∃! χ : ArchimedeanGL.EnvelopingCenter F (r + 1) →ₐ[ℂ] ℂ,
          ComplexPlaceParameter.MatchesInfinitesimalCharacter F (r + 1) ds χ) ∧
        ∀ χ : ArchimedeanGL.EnvelopingCenter F (r + 1) →ₐ[ℂ] ℂ,
          ComplexPlaceParameter.MatchesInfinitesimalCharacter F (r + 1) ds χ →
            S.realization.HasInfinitesimalCharacter χ

/-- Over a totally complex number field, a character `χ` of the actual center of the
enveloping algebra of rank `n` that matches a family `ds` of complex-character lists is
regular algebraic (`ArchimedeanGL.IsRegularAlgebraicCharacter`) exactly when every list
`ds v` is Clozel regular algebraic of rank `n`. -/
def ComplexParameterRegularAlgebraicTCStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [NumberField.IsTotallyComplex F] (n : ℕ)
    (ds : {v : NumberField.InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ),
    ComplexPlaceParameter.MatchesInfinitesimalCharacter F n ds χ →
      (ArchimedeanGL.IsRegularAlgebraicCharacter F n χ ↔
        ∀ v, ComplexPlaceParameter.IsClozelRegularAlgebraic n (ds v))

/-- The totally complex archimedean bridge: existence of complex-place parameters
(the existing `CuspidalArchimedeanParameterExistenceTCStatement`), their determination of the
infinitesimal character, and the comparison of regular algebraicity. -/
def CuspidalComplexParameterBridgeTCStatement : Prop :=
  Langlands.Global.CuspidalArchimedeanParameterExistenceTCStatement.{uF} ∧
    CuspidalComplexParameterInfinitesimalCharacterTCStatement.{uF} ∧
      ComplexParameterRegularAlgebraicTCStatement.{uF}

end Langlands.Automorphic
