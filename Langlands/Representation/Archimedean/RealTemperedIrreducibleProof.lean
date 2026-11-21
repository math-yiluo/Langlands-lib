import Langlands.Representation.Archimedean.RealTemperedFormProof
import Langlands.Representation.Archimedean.RealTemperedScalarCommutantProof

/-! # Irreducibility at equal real block exponents -/

set_option autoImplicit false

namespace Langlands.Archimedean

/-- The actual compact-finite real standard module of any rank-correct list of
blocks of equal real exponent is irreducible. -/
theorem realTemperedStandardIrreducible : RealTemperedStandardIrreducibleStatement :=
  realTemperedStandardIrreducible_of_form_of_scalarCommutant
    realTemperedForm realTemperedScalarCommutant

end Langlands.Archimedean
