import Langlands.GroupScheme.SimplyConnected.TypeE7KernelCenterInversion
import Langlands.GroupScheme.SimplyConnected.NormOneNonInvolutiveCenter
import Langlands.GroupScheme.SimplyConnected.TypeEAnisotropicKernelModel
import Langlands.GroupScheme.CenterAutomorphismBaseChange

/-! # Full-centre movement for actual branch-marked E7 kernels -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The precise proposition implemented by `hasCenterMovingAutomorphism_of_E7_branch_mark`. -/
def E7BranchMarkedCenterMovementStatement : Prop :=
  ∀ (e : d.Vertex ≃ Fin 7) (_hsc : IsSimplyConnected G)
    (_h : d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e)
    (_hstar : d.StarIsTrivial),
    HasCenterMovingAutomorphism d.anisotropicKernelIndex.kernel

/-- The actual anisotropic kernel of a simply connected branch-marked E7 index
with trivial full star admits an actual automorphism moving its full centre. -/
theorem hasCenterMovingAutomorphism_of_E7_branch_mark
    (e : d.Vertex ≃ Fin 7) (hsc : IsSimplyConnected G)
    (h : d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e)
    (hstar : d.StarIsTrivial) :
    HasCenterMovingAutomorphism d.anisotropicKernelIndex.kernel := by
  obtain ⟨n, hn⟩ := d.exists_normalizer_inverts_geometric_kernel_center_of_E7 hsc e h.1
  have hmodel := d.anisotropicKernel_divisionModel_of_E7_branch_mark e hsc h hstar
  obtain ⟨U, z, hz, hne⟩ := hmodel.exists_geometric_central_inv_ne (by decide)
  refine ⟨d.anisotropicKernelIndex.normalizerKernelIso n, fun hf => ?_⟩
  have hfix := (hf.baseChange (algebraBaseMap k (SeparableClosure k))) U z hz
  exact hne ((hn U z hz).symm.trans hfix)

end Langlands.GroupScheme.TitsIndexData
