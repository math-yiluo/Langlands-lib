import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealLeviChartIntegrable
import Langlands.Representation.Archimedean.RealLeviLanglandsQuotient
import Langlands.Representation.Archimedean.RealLeviParabolicIntegration
import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientProof
import Langlands.Representation.Archimedean.RealReverseIntertwinerKernel
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof

/-!
# Real generic standard parameters from classification and tied irreducibility

The classification step out of principal series gives an ordered quotient
map. Tied irreducibility gives the ordered quotient kernel theorem and
Speh's irreducibility criterion. Together with the proved large-quotient
and Whittaker results these make the parameter map injective.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe u

/-- The real classification step for principal-series quotients and tied
irreducibility imply existence of real generic standard parameters. -/
def RealGenericParameterFromTemperedStatement : Prop :=
  RealLanglandsFromPrincipalSeriesStatement.{u} →
    RealTemperedStandardIrreducibleStatement → RealGenericStandardParameterStatement.{u}

theorem realGenericParameterFromTempered : RealGenericParameterFromTemperedStatement.{u} := by
  intro hclass htied
  have hlq := realLeviLanglandsQuotient realLeviChartIntegrable realLeviParabolicIntegration htied
  have hrev :=
    realReverseIntertwinerKernelReduction realLeviChartIntegrable realLeviParabolicIntegration htied
  have hcriterion := realStandardIrreducibleCriterionReduction hlq realUnlinkedSwap hrev
  have hlarge := realLargeStandardIrreducibleReduction hcriterion realLinkedLanglandsQuotientNotLarge
  have hinj := realGenericLargeReduction InfinitesimalCharacter.realGKModuleInfinitesimalCharacter
    Kostant.realWhittakerMaximallyFaithful (realLargeLanglandsQuotientReduction hlq hlarge)
  exact realGenericStandardParameterReduction
    (realLanglandsQuotientReduction realPrincipalSeriesQuotient hclass) hinj

end Langlands.Archimedean
