import Langlands.Representation.Families.InducedTwistsUniformDetectionFromInputsStatement
import Langlands.Representation.Families.InducedTwistsDetectionReduction

/-! # Proof of the uniform induced-twist detector from its remaining inputs

The VI.9.4 Corollary, VI.9.6.1 second adjointness and the V.5.1–V.5.2 joint special-compact
basis imply the uniform compact-open detector used in the proof of Renard VI.8.4.
-/

set_option autoImplicit false

universe u v

namespace Langlands.Renard.AlgebraicFamily

/-- Proof of `InducedTwistsUniformDetectionFromInputsStatement`. -/
theorem inducedTwistsUniformDetectionFromInputs :
    InducedTwistsUniformDetectionFromInputsStatement.{u, v} :=
  fun hCor hAdj hJoint => inducedTwistsUniformDetection_of_inputs hCor hAdj hJoint

end Langlands.Renard.AlgebraicFamily
