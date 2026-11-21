import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealLargeStandardIrreducibleReduction
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.RealLeviLanglandsQuotient
import Langlands.Representation.Archimedean.RealLeviChartIntegrable
import Langlands.Representation.Archimedean.RealLeviParabolicIntegration
import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealTemperedFormProof
import Langlands.Representation.Archimedean.RealReverseIntertwinerKernel
import Langlands.Representation.Archimedean.RealTiedScalarCommutantCases
import Langlands.Representation.Archimedean.RealTiedDiscreteScalarCommutantCases
import Langlands.Representation.Archimedean.RealTiedScalarAssembly
import Langlands.Representation.Archimedean.RealSphericalCyclicProof
import Langlands.Representation.Archimedean.RealDiscreteSeparatedProof
import Langlands.Representation.Archimedean.RealDiscreteCoincidentProof

/-!
# Injectivity of maps onto large Langlands quotients of `GL_n(ℝ)`

The three scalar-commutant cases give irreducible tie classes. The Levi-limit arguments
then give the largest proper submodule and control the kernel of a reverse intertwiner.
The unlinked criterion and the linked quotient growth bound together show that the
largest proper submodule is zero when the quotient is maximally faithful.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- Every nonzero intertwiner from a Langlands-ordered real standard module into
an irreducible admissible maximally faithful module is injective. -/
theorem realLargeLanglandsQuotientInjective : RealLargeLanglandsQuotientInjectiveStatement.{uV} :=
  have hScal : RealTemperedScalarCommutantStatement :=
    realTemperedScalarCommutant_of_cases
      (realTiedNondiscreteReduction RealSphericalCyclicProof.realSphericalCyclic)
      (realTiedDiscreteScalarCommutant_of_cases realTiedDiscreteSeparatedScalarCommutant
        realTiedDiscreteCoincidentScalarCommutant)
  have hTemp : RealTemperedStandardIrreducibleStatement :=
    realTemperedStandardIrreducible_of_form_of_scalarCommutant realTemperedForm hScal
  have hL : RealStandardLanglandsQuotientStatement :=
    realLeviLanglandsQuotient realLeviChartIntegrable realLeviParabolicIntegration hTemp
  have hRev : RealReverseIntertwinerKernelStatement :=
    realReverseIntertwinerKernelReduction realLeviChartIntegrable realLeviParabolicIntegration
      hTemp
  realLargeLanglandsQuotientReduction hL
    (realLargeStandardIrreducibleReduction
      (realStandardIrreducibleCriterionReduction hL realUnlinkedSwap hRev)
      realLinkedLanglandsQuotientNotLarge)

end Langlands.Archimedean
