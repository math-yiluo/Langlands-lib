import Langlands.GroupScheme.Cohomology.DifferentialRepresentation
import Langlands.GroupScheme.Cohomology.SourceTransport
import Langlands.GroupScheme.Cohomology.TensorCoefficients

/-! # Actual adjoint coefficients for homomorphism deformation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- The actual coefficient representation obtained from the adjoint action of
the target, restriction along the supplied homomorphism, and tensoring with an
arbitrary base coefficient module. -/
def homomorphismCoefficients (f : H ⟶ G) (N : Type u) [AddCommGroup N] [Module R N] :
    ModuleRepresentation (Additive (lieKernel G R) ⊗[R] N) H :=
  ((adjointModuleRepresentation G).tensorTrivial N).precomp f

/-- The coefficient module action has the prescribed adjoint action on the
Lie factor and the trivial action on the extra coefficient factor. -/
theorem homomorphismCoefficients_action (f : H ⟶ G)
    (N : Type u) [AddCommGroup N] [Module R N] (A : CommAlgCat.{u} R)
    (h : H.affinePoints A) (x : ModulePoints (Additive (lieKernel G R)) A) (n : N) :
    (homomorphismCoefficients f N).action A h
        (tensorCoefficientPoint (Additive (lieKernel G R)) N A x n) =
      tensorCoefficientPoint (Additive (lieKernel G R)) N A
        ((adjointModuleRepresentation G).action A (H.affinePointsTarget f A h) x) n :=
  ModuleRepresentation.tensorAction_point (adjointModuleRepresentation G)
    N A (H.affinePointsTarget f A h) x n

end Langlands.GroupScheme.Cohomology
