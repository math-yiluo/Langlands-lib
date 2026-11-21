import Langlands.Representation.Archimedean.RealTiedScalarAssembly
import Langlands.Representation.Archimedean.RealSphericalCyclicProof
import Langlands.Representation.Archimedean.RealTiedDiscreteScalarCommutantCases
import Langlands.Representation.Archimedean.RealDiscreteSeparatedProof
import Langlands.Representation.Archimedean.RealDiscreteCoincidentProof

/-! # The scalar commutant of tied real standard modules -/

set_option autoImplicit false

namespace Langlands.Archimedean

/-- On the actual compact-finite real standard module of a tied, rank-correct block list,
every simultaneous compact and complexified Lie endomorphism is scalar. -/
theorem realTemperedScalarCommutant : RealTemperedScalarCommutantStatement :=
  realTemperedScalarCommutant_of_cases
    (realTiedNondiscreteReduction RealSphericalCyclicProof.realSphericalCyclic)
    (realTiedDiscreteScalarCommutant_of_cases
      realTiedDiscreteSeparatedScalarCommutant realTiedDiscreteCoincidentScalarCommutant)

end Langlands.Archimedean
