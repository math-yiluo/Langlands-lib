import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate
import Langlands.GroupScheme.CoalgebraUnipotence.Definitions

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.UnipotentMatrixCriterion

/-- Actual unipotence of a corepresented group is the finite coefficient-matrix criterion
for its coordinate bialgebra. -/
def CorepresentedMatrixUnipotenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u})
    (B : CommAlgCat.{u} (CommRingCat.of k))
    (e : (F ⋙ forget GrpCat).CorepresentableBy B),
    letI := AffineLinearEmbedding.bialgebra e
    IsUnipotent (Corepresented.groupScheme F e) ↔
      CoalgebraUnipotence.IsMatrixUnipotent k B

end Langlands.GroupScheme.UnipotentMatrixCriterion
