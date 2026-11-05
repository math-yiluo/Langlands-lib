import Langlands.GroupScheme.AlgebraicallyClosedSplitSolvableStatement
import Langlands.GroupScheme.SplitSolvableSmoothExtension
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientReduction
import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryProof
import Langlands.GroupScheme.Unipotent.AlgebraicallyClosedSplit

/-! # Represented split series for solvable groups over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every smooth connected solvable affine group over an algebraically closed
field has a finite represented Ga/Gm series. -/
theorem algebraicallyClosedSplitSolvable :
    AlgebraicallyClosedSplitSolvableStatement.{u} := by
  intro k _ _ G _ _ hc hs
  let : ConnectedSpace G.X.left := hc
  obtain ⟨N, Q, i, q, hi, hnsm, hnc, hnu, _, hquot, hQ⟩ :=
    solvableTorusQuotient_of_kernel_prerequisites
      triangularDiagonalKernelGeometry unipotentClosedSubgroup k G hs
  let : Smooth N.X.hom := hnsm
  let : ConnectedSpace N.X.left := hnc
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom N.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient
    i q hi hquot hs (Unipotent.algebraicallyClosedSplit k N hnc hnu) hQ

end Langlands.GroupScheme
