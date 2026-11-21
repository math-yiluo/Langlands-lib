import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientInjectiveProof

/-!
# Injectivity of maps from standard modules onto generic `(𝔤𝔩_n(ℝ), O(n))`-modules

The published reduction `realGenericLargeReduction` derives
`RealGenericLanglandsQuotientInjectiveStatement` from three statements: every irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module has an infinitesimal character, Kostant's theorem
(a generic module with an infinitesimal character is maximally faithful), and Vogan's theorem
(nonzero intertwiners from Langlands-ordered standard modules onto irreducible admissible
maximally faithful modules are injective). All three are proved in the Library; this file
applies the reduction to these three theorems.
-/

namespace Langlands.Archimedean

universe uV

/-- Every nonzero intertwiner from the `O(n)`-finite functions of a Langlands-ordered real
standard module of total rank `n` into an irreducible admissible generic
`(𝔤𝔩_n(ℝ), O(n))`-module is injective. -/
theorem realGenericLanglandsQuotientInjective :
    RealGenericLanglandsQuotientInjectiveStatement.{uV} :=
  realGenericLargeReduction InfinitesimalCharacter.realGKModuleInfinitesimalCharacter
    Kostant.realWhittakerMaximallyFaithful realLargeLanglandsQuotientInjective

end Langlands.Archimedean
