import Langlands.GroupScheme.Reductive.CentralResidueKernelMultiplicativeType
import Langlands.GroupScheme.Reductive.GlobalKernelCentrality
import Langlands.GroupScheme.Torus.FiniteFlatArtinianCentrality

/-! # The fibrewise central-isogeny criterion for reductive group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace FibrewiseCentralIsogenyProof

/-- The focused finite-flat local Artinian kernel-centrality input holds
without any retained structural premise. -/
theorem finiteFlatArtinianKernelCentrality :
    NoetherianKernelCentrality.FiniteFlatArtinianKernelCentralityStatement.{u} := by
  intro R _ _ _ G H hG hH f _ hf _ hfin hc
  let := hG.isAffineHom
  let := hH.isAffineHom
  let := hfin
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine (kernel f).X.left :=
    isAffine_of_isAffineHom (kernel f).X.hom
  have : Flat (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf
  apply FiniteFlatArtinianCentrality.isCentral_of_multiplicativeType_residue R (kernelι f)
  · exact CentralResidueKernelMultiplicativeType.isMultiplicativeType_kernel_fieldFiber
      hG f hc (Spec.algebraMap R (IsLocalRing.ResidueField R))
  · exact CentralResidueKernelMultiplicativeType.isCentral_field_baseChange_of_residue
      (kernelι f)
      (fun s => (KernelInfinitesimalCentrality.isCentral_kernel_baseChange_iff
        _ f).1 (hc s))
      (Spec.algebraMap R (IsLocalRing.ResidueField R))

end FibrewiseCentralIsogenyProof

/-- The unchanged fibrewise central-isogeny criterion for reductive group
schemes over every scheme base. -/
theorem reductiveFibrewiseCentralIsogeny : ReductiveFibrewiseCentralIsogenyStatement.{u} :=
  GlobalKernelCentrality.criterion_of_artinianInput
    FibrewiseCentralIsogenyProof.finiteFlatArtinianKernelCentrality

end Langlands.GroupScheme
