import Langlands.LocalFactor.BrauerKernel.GlobalAssembly
import Langlands.ClassField.Global.LocalRelativeWeilTransferProof

/-! # Proof of the actual abelian epsilon Brauer-kernel compatibility -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

/-- **Brauer-kernel compatibility** (Deligne 1973, Lemma 4.7 and the global argument of §4.12,
in the derived continuous common-closure form). For every prime `p`, every p-adic field `F`,
every supplied normalized reciprocity family `e`, every intermediate field `E`, every nontrivial
unitary additive character `ψ` of `E` and every family of regular additive Haar measures, the
actual abelian epsilon-ratio evaluation vanishes on the kernel of the actual Brauer presentation
of the continuous exact degree-zero group. -/
theorem kernelCompatibilityStatement : KernelCompatibilityStatement.{uF, uV} :=
  kernelCompatibilityStatement_of_localTransferReciprocity.{uF, uV}
    ClassField.Global.RelativeWeilGroup.localTransferReciprocity.{0}

end Langlands.LocalFactor.NonabelianBrauer
