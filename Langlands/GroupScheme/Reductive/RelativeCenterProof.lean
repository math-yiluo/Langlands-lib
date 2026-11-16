import Langlands.GroupScheme.Reductive.RelativeCenterStatement
import Langlands.GroupScheme.Reductive.RelativeCenterDescent
import Langlands.GroupScheme.Reductive.AffinePinnedAtlas
import Langlands.GroupScheme.Reductive.RootKernelCenter

/-! # The scheme-theoretic centre of a reductive group over a base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- The relative-centre theorem reduces to diagonalizable centre
representatives for affine pinned models. -/
theorem reductiveRelativeCenter_of_affinePinnedModels
    (h : ∀ M : AffinePinnedModel.{u},
      ∃ (Z : GroupScheme M.base) (z : Z ⟶ M.group),
        IsSchemeTheoreticCenter z ∧ RelativeMultiplicativeType.IsDiagonalizable Z) :
    ReductiveRelativeCenterStatement.{u} := by
  intro S G hG
  let A := AffinePinnedAtlas.ofReductive hG
  apply exists_multiplicativeTypeCenter_of_etaleCover A.cover
  intro k
  obtain ⟨Z, z, hZ, hdiag⟩ := h (A.chart k).model
  exact ⟨Z, z ≫ (A.chart k).iso.inv, hZ.comp_iso (A.chart k).iso.symm, hdiag⟩

/-- The full centre of a reductive group over any scheme is closed and of
multiplicative type, and its inclusion remains the full centre after every
base change. -/
theorem reductiveRelativeCenter : ReductiveRelativeCenterStatement.{u} := by
  apply reductiveRelativeCenter_of_affinePinnedModels
  intro M
  exact ⟨M.centerKernel, M.centerKernelHom,
    M.centerKernel_isSchemeTheoreticCenter, M.centerKernel_isDiagonalizable⟩

end Langlands.GroupScheme
