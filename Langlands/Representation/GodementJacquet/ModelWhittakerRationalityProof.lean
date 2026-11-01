import Langlands.Representation.GodementJacquet.WhittakerModelRationality
import Langlands.Representation.Whittaker.TypeAsymptoticProof
import Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof

/-!
# Convergence and rationality of Whittaker matrix integrals on the model

The conditional coefficient-model theorem is applied to the full Whittaker
torus asymptotic theorem and finite-function Mellin theorem. See the paired
Markdown for the implemented proof and its source provenance.
-/

noncomputable section

namespace Langlands.GodementJacquet

universe uF uV

/-- Every shifted full-matrix Whittaker integral on the coefficient model
converges on a right half-plane and has a rational continuation in `q^(-s)`. -/
theorem modelWhittakerRationality : ModelWhittakerRationalityStatement.{uF, uV} :=
  WhittakerTorus.Padic.modelWhittakerRationality.{uF, uV}
    Langlands.whittakerTypeAsymptotic.{uF, uV}
    Langlands.RankinSelberg.finiteFunctionMellin.{uF}

end Langlands.GodementJacquet
