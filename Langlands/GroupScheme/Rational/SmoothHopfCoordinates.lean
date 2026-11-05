import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Smooth Hopf coordinates and scalar extension -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]
  [Smooth G.X.hom]

set_option linter.defProp false in
/-- The chosen Hopf coordinate algebra of a smooth affine group scheme is smooth. -/
@[instance_reducible]
def hopfAlgebraSmooth : Algebra.Smooth R (hopfAlgebra G) :=
  smooth_algebra G inferInstance

attribute [instance] hopfAlgebraSmooth

variable (B : Type v) [CommRing B] [Algebra R B]

/-- Scalar extension of the chosen smooth Hopf coordinate algebra is smooth. -/
theorem hopfAlgebraBaseChange_smooth :
    Algebra.Smooth B (B ⊗[R] hopfAlgebra G) :=
  inferInstance

/-- Scalar extension of the chosen smooth Hopf coordinate algebra is finite type. -/
theorem hopfAlgebraBaseChange_finiteType :
    Algebra.FiniteType B (B ⊗[R] hopfAlgebra G) :=
  inferInstance

set_option linter.defProp false in
/-- Scalar extension to any domain of smooth affine Hopf coordinates is reduced. -/
@[instance_reducible]
def hopfAlgebraBaseChangeReduced [IsDomain B] :
    IsReduced (B ⊗[R] hopfAlgebra G) :=
  Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain B _

attribute [instance] hopfAlgebraBaseChangeReduced

end Langlands.GroupScheme.AffineCoordinates
