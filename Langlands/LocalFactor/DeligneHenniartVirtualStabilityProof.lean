import Langlands.LocalFactor.DeligneHenniartVirtualReduction
import Langlands.LocalFactor.DeligneHenniartIntermediateGeometricProof
import Langlands.LocalFactor.DeligneHenniartTopLayerProof
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof
import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityFiniteReduction
import Langlands.ClassFieldTheory.Local.UpperReciprocityNormReduction
import Langlands.ClassFieldTheory.Local.NormUnitImageCardinalityProof

/-!
# Proof of Deligne–Henniart wild virtual stability (DH81 Theorem 4.6)

`virtualStability_of_inputs` reduces `VirtualStabilityStatement` to four propositions; this
module supplies the Library proofs of all four.
-/

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

universe uF uV

/-- **Deligne–Henniart 1981, Theorem 4.6 with (4.2.2).** Wild virtual stability holds for every
system and every virtual Weil representation with positive breaks, with no further hypotheses. -/
theorem virtualStabilityProof : VirtualStabilityStatement.{uF, uV} :=
  virtualStability_of_inputs
    (LocalClassField.absoluteUpperReciprocityTheorems_of_finiteRealImages
      (LocalClassField.finiteReciprocityRealUnitImages_of_normCardinality
        LocalClassField.NormUnitImage.finiteAbelianNormUnitImageCardinality.{uF, uF})).2.2.1
    LocalClassField.commonClosureGeometricProof.{uF, uF}
    intermediateGeometricProof.{uF}
    TopLayer.topLayerNormTrace.{uF, uF, uF}

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
