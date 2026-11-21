import Langlands.Representation.Archimedean.RealLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientProof
import Langlands.Representation.Archimedean.RealLanglandsFromPrincipalSeriesProof
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientInjectiveProof

/-!
# Irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-modules have standard-module parameters

`realGenericStandardParameter` proves `RealGenericStandardParameterStatement`: every
irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module has the standard-module parameter of
some list of real blocks.

The proof applies the published reduction `realGenericStandardParameterReduction` to the
two statements it needs, each obtained from a published reduction and proved Library theorems:

* `RealLanglandsQuotientStatement` (Langlands classification, existence half), by
  `realLanglandsQuotientReduction` from Casselman's theorem in quotient form
  (`realPrincipalSeriesQuotient`) and the Langlands classification starting from a
  principal-series quotient (`realLanglandsFromPrincipalSeries`);
* `RealGenericLanglandsQuotientInjectiveStatement` (injectivity of nonzero intertwiners from a
  Langlands-ordered standard module into a generic module), by `realGenericLargeReduction` from
  the existence of infinitesimal characters
  (`InfinitesimalCharacter.realGKModuleInfinitesimalCharacter`), Kostant's theorem
  (`Kostant.realWhittakerMaximallyFaithful`) and Vogan's theorem
  (`realLargeLanglandsQuotientInjective`).
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- The existence half of the Langlands classification of `GL_n(ℝ)`: every irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module is a nonzero quotient of the `O(n)`-finite part of a
standard module in Langlands order. -/
theorem realLanglandsQuotient_of_principalSeries : RealLanglandsQuotientStatement.{uV} :=
  realLanglandsQuotientReduction realPrincipalSeriesQuotient realLanglandsFromPrincipalSeries

/-- A nonzero intertwiner from the `O(n)`-finite part of a Langlands-ordered standard module of
`GL_n(ℝ)` into an irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module is injective. -/
theorem realGenericLanglandsQuotientInjective_of_large :
    RealGenericLanglandsQuotientInjectiveStatement.{uV} :=
  realGenericLargeReduction InfinitesimalCharacter.realGKModuleInfinitesimalCharacter
    Kostant.realWhittakerMaximallyFaithful realLargeLanglandsQuotientInjective

/-- **Generic modules have standard-module parameters** (`GL_n(ℝ)`): every irreducible
admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module receives an injective `(𝔤, K)`-intertwiner from the
`O(n)`-finite part of the standard module of some list of real blocks of total rank `n`. -/
theorem realGenericStandardParameter : RealGenericStandardParameterStatement.{uV} :=
  realGenericStandardParameterReduction realLanglandsQuotient_of_principalSeries
    realGenericLanglandsQuotientInjective_of_large

end Langlands.Archimedean
