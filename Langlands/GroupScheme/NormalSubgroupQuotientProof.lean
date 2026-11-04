import Langlands.GroupScheme.NormalSubgroupQuotientAlgClosedReduction
import Langlands.GroupScheme.MatrixRepresentation.NormalKernel
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Smooth affine quotients by normal closed subgroups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The exact normal-kernel representation supplies the algebraically
closed-field affine-kernel construction input. -/
theorem algClosedNormalSubgroupAffineKernel :
    AlgClosedNormalSubgroupAffineKernelStatement.{u} := by
  intro k _ _ G _ _ N i hc hN
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  let D := MatrixRepresentation.normalKernelRepresentation i hc hN
  have : Smooth (GeneralLinear.groupScheme (Fin D.dimension) (CommRingCat.of k)).X.hom :=
    GeneralLinear.smoothStatement (Fin D.dimension) (CommRingCat.of k)
  exact ⟨GeneralLinear.groupScheme (Fin D.dimension) (CommRingCat.of k),
    D.representation, GeneralLinear.isAffineHom_groupScheme _ _,
    inferInstance, D.kernel_range⟩

/-- Every normal closed subgroup of a smooth affine group over an arbitrary
field is the full kernel of an fppf map onto a smooth affine group. -/
theorem normalSubgroupQuotient : NormalSubgroupQuotientStatement.{u} :=
  normalSubgroupQuotient_of_algClosed_affineKernel algClosedNormalSubgroupAffineKernel

end Langlands.GroupScheme
