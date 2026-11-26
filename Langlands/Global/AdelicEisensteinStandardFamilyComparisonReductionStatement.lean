import Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement
import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Global.AdelicLeadingCuspidalInjectivityStatement
import Langlands.Global.AdelicCuspidalProjectionDecompositionStatement
import Langlands.Global.AdelicLeviCuspFormMajorantStatement

/-! # Inputs of the regular-patch Eisenstein comparison for finite families -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- The comparison for finite families of inducing data follows from the meromorphic
continuation of Eisenstein series, the injectivity of leading cuspidal components, the
convergent expansion of the cuspidal tests, the cuspidal projections with their exponent
decompositions, and the integrable weighted majorants of Levi cusp forms. -/
def StandardEisensteinFamilyComparisonReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{u} → LeadingCuspidalInjectivityStatement.{u} →
    ConvergentCuspidalTestExpansionStatement.{u} → CuspidalProjectionDecompositionStatement.{u} →
    LeviCuspFormPairingMajorantStatement.{u} → StandardEisensteinFamilyComparisonStatement.{u}

end Langlands.Global
