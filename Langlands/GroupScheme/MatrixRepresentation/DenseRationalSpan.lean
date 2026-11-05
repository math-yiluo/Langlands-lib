import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.LinearAlgebra.IrreducibleRepresentationSpan

/-! # Matrix span from a dense rational-point monoid -/

noncomputable section

universe u v

open AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {I : Type v} [Monoid I]
  {J : GroupScheme (Spec (CommRingCat.of k))} [IsReduced J.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

/-- A dense monoid family in an all-test irreducible representation spans the
full matrix algebra over an algebraically closed field. -/
theorem span_rationalMatrix_comp_eq_top_of_dense
    (ρ : MatrixRepresentation J n) (hρ : ρ.IsIrreducible)
    (α : I →* Langlands.AlgebraicGeometry.PointTopology.RationalPoint k J.X)
    (hα : Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPointFamily α) :
    Submodule.span k
      (Set.range fun i => (ρ.rationalMatrix (α i) : Matrix n n k)) = ⊤ := by
  let : Representation.IsIrreducible
      (Langlands.LinearAlgebra.matrixAction (ρ.rationalMatrix.comp α)) :=
    ρ.irreducible_rationalAction_comp hρ α hα
  exact Langlands.LinearAlgebra.matrix_span_eq_top_of_irreducible
    (ρ.rationalMatrix.comp α)

end Langlands.GroupScheme.MatrixRepresentation
