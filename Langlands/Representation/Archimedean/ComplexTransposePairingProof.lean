import Langlands.Representation.Archimedean.ComplexTransposePairingReduction
import Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof
import Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationProof
import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof

/-! # Inverse-transpose pairing for irreducible admissible complex GK modules -/

set_option autoImplicit false

universe uV

namespace Langlands.Archimedean

/-- Every irreducible admissible complex GK module admits a nonzero bilinear form
invariant for the original and actual inverse-transpose actions. -/
theorem complexTransposePairing : ComplexTransposePairingStatement.{uV} :=
  ComplexTransposePairingReduction.complexTransposePairing_of_langlands
    (complexBlockLanglandsQuotient complexBlockChartIntegrable
      complexBlockParabolicIntegration complexTemperedStandardIrreducible)

end Langlands.Archimedean
