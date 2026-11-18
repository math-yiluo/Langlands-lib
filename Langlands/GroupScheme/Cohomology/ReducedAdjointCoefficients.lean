import Langlands.GroupScheme.Cohomology.BaseChange
import Langlands.GroupScheme.Cohomology.CoefficientTransport
import Langlands.GroupScheme.Cohomology.HomomorphismCoefficients
import Langlands.GroupScheme.Lie.ReducedKernelCoefficients

/-! # Actual adjoint representations on quotient-base ideal coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable [IsAffineHom G.X.hom] (I : Ideal R)

/-- Regroup a scalar-extended Lie vector and a trivial ideal cotangent factor
as the canonical quotient-base reduction coefficient module. -/
def reducedAdjointCoefficientEquiv :
    (((R ⧸ I) ⊗[R] Additive (lieKernel G R)) ⊗[R ⧸ I] I.Cotangent) ≃ₗ[R ⧸ I]
      Lie.SquareZero.reducedKernelModule G I :=
  (TensorProduct.comm (R ⧸ I) _ I.Cotangent).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I)
      I.Cotangent (Additive (lieKernel G R)))

@[simp]
theorem reducedAdjointCoefficientEquiv_tmul (c : R ⧸ I)
    (X : Additive (lieKernel G R)) (i : I.Cotangent) :
    reducedAdjointCoefficientEquiv G I ((c ⊗ₜ[R] X) ⊗ₜ[R ⧸ I] i) =
      (c • i) ⊗ₜ[R] X := rfl

@[simp]
theorem reducedAdjointCoefficientEquiv_symm_tmul
    (X : Additive (lieKernel G R)) (i : I.Cotangent) :
    (reducedAdjointCoefficientEquiv G I).symm (i ⊗ₜ[R] X) =
      ((1 : R ⧸ I) ⊗ₜ[R] X) ⊗ₜ[R ⧸ I] i := rfl

variable [Smooth G.X.hom]

/-- The actual adjoint representation, base changed to the quotient ring and
tensored with its trivial ideal cotangent module. -/
def reducedAdjointModuleRepresentation :
    ModuleRepresentation (R := CommRingCat.of (R ⧸ I))
      (Lie.SquareZero.reducedKernelModule G I)
      ((GroupScheme.baseChange (algebraBaseMap R (R ⧸ I))).obj G) :=
  (((adjointModuleRepresentation G).baseChange (CommAlgCat.of R (R ⧸ I))).tensorTrivial
    I.Cotangent).congr (reducedAdjointCoefficientEquiv G I)

/-- Restrict the actual reduced adjoint coefficient representation along an
actual reduced homomorphism. -/
def reducedHomomorphismCoefficients
    {H₀ : GroupScheme (Spec (CommRingCat.of (R ⧸ I)))}
    (f₀ : H₀ ⟶ (GroupScheme.baseChange (algebraBaseMap R (R ⧸ I))).obj G) :
    ModuleRepresentation (Lie.SquareZero.reducedKernelModule G I) H₀ :=
  (reducedAdjointModuleRepresentation G I).precomp f₀

end Langlands.GroupScheme.Cohomology
