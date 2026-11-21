import Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction
import Langlands.Automorphic.ArchimedeanParameterReduction
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker
import Langlands.Representation.Archimedean.ComplexGenericStandardParameterProof
import Langlands.Representation.Archimedean.RealGenericParameterReduction
import Langlands.Representation.Archimedean.RealLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientProof
import Langlands.Representation.Archimedean.RealLanglandsFromPrincipalSeriesProof
import Langlands.Representation.Archimedean.RealGenericLargeReduction
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientInjectiveProof

/-! # Archimedean standard-module parameters of actual cuspidal realizations

`cuspidalArchimedeanParameterExistence` proves `CuspidalArchimedeanParameterExistenceStatement`:
every actual cuspidal realization of `GL_(r+1)` over a number field has a standard-module
parameter at every real and every complex place.

The proof applies the published reduction `cuspidalArchimedeanParameterReduction` to three
proved inputs:

* the `GL_n(ℝ)` input `RealGenericStandardParameterStatement`, obtained by composing the
  published reductions `Archimedean.realGenericStandardParameterReduction`,
  `Archimedean.realLanglandsQuotientReduction` and `Archimedean.realGenericLargeReduction` with
  the five proved theorems `realPrincipalSeriesQuotient`, `realLanglandsFromPrincipalSeries`,
  `InfinitesimalCharacter.realGKModuleInfinitesimalCharacter`,
  `Kostant.realWhittakerMaximallyFaithful` and `realLargeLanglandsQuotientInjective`;
* the `GL_n(ℂ)` theorem `Archimedean.complexGenericStandardParameter`;
* the global generic-component statement, `cuspidalArchimedeanGenericComponentBridge` applied
  to `cuspidalArchimedeanIrreducibleAdmissibleComponent` and
  `cuspidalArchimedeanWhittakerFunctional`.
-/

universe u

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Automorphic

/-- **Archimedean standard-module parameters of actual cuspidal realizations.** For every
number field `F` with compact adele quotient, every `r` and every actual cuspidal realization
`T` of `GL_(r+1)`, the realization has a real standard-module parameter at every real place
and a complex one at every complex place. -/
theorem cuspidalArchimedeanParameterExistence :
    CuspidalArchimedeanParameterExistenceStatement.{u} :=
  cuspidalArchimedeanParameterReduction
    (Archimedean.realGenericStandardParameterReduction
      (Archimedean.realLanglandsQuotientReduction Archimedean.realPrincipalSeriesQuotient
        Archimedean.realLanglandsFromPrincipalSeries)
      (Archimedean.realGenericLargeReduction
        Archimedean.InfinitesimalCharacter.realGKModuleInfinitesimalCharacter
        Archimedean.Kostant.realWhittakerMaximallyFaithful
        Archimedean.realLargeLanglandsQuotientInjective))
    Archimedean.complexGenericStandardParameter
    (cuspidalArchimedeanGenericComponentBridge cuspidalArchimedeanIrreducibleAdmissibleComponent
      cuspidalArchimedeanWhittakerFunctional)

end Langlands.Global
