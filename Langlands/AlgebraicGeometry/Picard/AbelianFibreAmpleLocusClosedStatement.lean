import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingStatement

/-! # Closedness of the fibrewise ample locus on an abelian scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a specified line bundle on an abelian scheme over a locally noetherian
base, the locus of base points with ample residue-field fibre is closed. -/
def AbelianFibreAmpleLocusClosedStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (A : Langlands.AbelianScheme S)
    (L : LineBundle A.X.left),
    IsClosed {s : S | ((LineBundle.pullback (A.X.hom.fiberι s)).obj L).IsAmple}

end Langlands.AlgebraicGeometry.Picard
