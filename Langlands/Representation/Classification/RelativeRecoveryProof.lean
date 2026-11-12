import Langlands.Representation.Classification.SupportedRelativeRecoveryProof
import Langlands.Representation.Classification.TemperedRelativeQuotientReflectionProof

/-! Supported recovery and arbitrary-tempered fine quotient reflection. -/

namespace Langlands

universe uF uV uM uW uX uZ

/-- The exact relative recovery conjunction, retaining every independent
carrier universe and both distinct support scopes. -/
theorem glRelativeRecovery :
    GLRelativeRecoveryStatement.{uF,uV,uM,uW,uX,uZ} :=
  ⟨glSupportedRelativeRecovery.{uF,uV,uM,uW,uX,uZ},
    glTemperedRelativeQuotientReflection.{uF,uV,uM,uW,uZ}⟩

end Langlands
