import Langlands.GroupScheme.Lie.FlatKernelCoefficients
import Langlands.CommutativeAlgebra.SquareZeroCotangentCoefficients

/-! # Actual square-zero kernel coefficients over the quotient base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie.SquareZero

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

/-- A canonical quotient-base module for the ideal and the original base Lie
module; the cotangent quotient supplies its quotient scalar action. -/
abbrev reducedKernelModule (I : Ideal R) := I.Cotangent ⊗[R] Additive (lieKernel G R)

/-- The actual quotient-base scalar extension of an affine test algebra. -/
abbrev reducedTestAlgebra (I : Ideal R) (B : CommAlgCat.{u} R) :
    CommAlgCat.{u} (R ⧸ I) :=
  CommAlgCat.of (R ⧸ I) ((R ⧸ I) ⊗[R] B)

variable [Smooth G.X.hom]
variable (I : Ideal R) (hI : I ^ 2 = ⊥) (B : CommAlgCat.{u} R) [Module.Flat R B]

local instance reducedTestRightAlgebra (C : CommAlgCat.{u} R) :
    Algebra C ((R ⧸ I) ⊗[R] C) := Algebra.TensorProduct.rightAlgebra

/-- On a flat affine test, the actual reduction kernel is exactly the scalar
extension of the canonical quotient-base coefficient module. -/
def reducedKernelCoefficientEquiv :
    Additive (kernel G (I.map (algebraMap R B))) ≃+
      Cohomology.ModulePoints (R := CommRingCat.of (R ⧸ I)) (reducedKernelModule G I) (reducedTestAlgebra I B) :=
  (flatKernelCoefficientEquiv G I hI B).trans
    (Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
      (Additive (lieKernel G R)) B).symm.toAddEquiv

/-- Reconstruct the actual group point from a quotient-base coefficient. -/
def reducedKernelPoint
    (z : Cohomology.ModulePoints (R := CommRingCat.of (R ⧸ I)) (reducedKernelModule G I) (reducedTestAlgebra I B)) :
    AffinePoints G B :=
  flatKernelPoint G I hI B
    (Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
      (Additive (lieKernel G R)) B z)

@[simp]
theorem reducedKernelPoint_add
    (z w : Cohomology.ModulePoints (R := CommRingCat.of (R ⧸ I)) (reducedKernelModule G I) (reducedTestAlgebra I B)) :
    reducedKernelPoint G I hI B (z + w) =
      reducedKernelPoint G I hI B z * reducedKernelPoint G I hI B w := by
  simp only [reducedKernelPoint, LinearEquiv.map_add, flatKernelPoint_add]

/-- A pure quotient-base tensor reconstructs the corresponding actual tangent
point in the extended base ideal. -/
theorem reducedKernelPoint_one_tmul (b : B) (i : I) (X : Additive (lieKernel G R)) :
    reducedKernelPoint G I hI B
      (((1 : R ⧸ I) ⊗ₜ[R] b) ⊗ₜ[R ⧸ I] (I.toCotangent i ⊗ₜ[R] X)) =
      (tangentPoint G (I.map (algebraMap R B)) (extendedIdeal_square I hI B)
        ((Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv
          (R := B) I) (b ⊗ₜ[R] i))
        (lieKernelMap G (Algebra.ofId R B) X.toMul)).val := by
  rw [reducedKernelPoint,
    Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv_one_tmul,
    flatKernelPoint_tmul]

/-- The quotient-base reconstruction recovers the given actual kernel point. -/
theorem reducedKernelPoint_coefficient
    (x : kernel G (I.map (algebraMap R B))) :
    reducedKernelPoint G I hI B
      (reducedKernelCoefficientEquiv G I hI B (Additive.ofMul x)) = x.val := by
  change flatKernelPoint G I hI B
    ((Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
      (Additive (lieKernel G R)) B)
      ((Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
        (Additive (lieKernel G R)) B).symm
        (flatKernelCoefficientEquiv G I hI B (Additive.ofMul x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [flatKernelPoint, AddEquiv.symm_apply_apply,
    Additive.toMul, Equiv.symm_apply_apply]

/-- Reconstructed actual points reduce to the identity. -/
theorem reducedKernelPoint_reduction
    (z : Cohomology.ModulePoints (R := CommRingCat.of (R ⧸ I)) (reducedKernelModule G I) (reducedTestAlgebra I B)) :
    reduction G (I.map (algebraMap R B)) (reducedKernelPoint G I hI B z) = 1 :=
  flatKernelPoint_reduction G I hI _

variable {B} {C : CommAlgCat.{u} R} [Module.Flat R C]

/-- Actual point reconstruction commutes with change of flat test algebra on
the quotient-base coefficient module. -/
theorem reducedKernelPoint_naturality (f : B ⟶ C)
    (z : Cohomology.ModulePoints (R := CommRingCat.of (R ⧸ I)) (reducedKernelModule G I) (reducedTestAlgebra I B)) :
    affineMap G f.hom (reducedKernelPoint G I hI B z) =
      reducedKernelPoint G I hI C
        (Cohomology.modulePointMap (R := CommRingCat.of (R ⧸ I)) (reducedKernelModule G I)
          (CommAlgCat.ofHom (Langlands.CommutativeAlgebra.SquareZero.quotientTestMap I f.hom)) z) := by
  rw [reducedKernelPoint, reducedKernelPoint, flatKernelPoint_naturality]
  congr 1
  exact (Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv_naturality
    I hI (Additive (lieKernel G R)) f.hom z).symm

/-- Forward naturality of the quotient-base coefficients for compatible actual
kernel points on flat affine tests. -/
theorem reducedKernelCoefficientEquiv_naturality (f : B ⟶ C)
    (x : kernel G (I.map (algebraMap R B)))
    (y : kernel G (I.map (algebraMap R C)))
    (hxy : affineMap G f.hom x.val = y.val) :
    reducedKernelCoefficientEquiv G I hI C (Additive.ofMul y) =
      Cohomology.modulePointMap (R := CommRingCat.of (R ⧸ I)) (reducedKernelModule G I)
        (CommAlgCat.ofHom (Langlands.CommutativeAlgebra.SquareZero.quotientTestMap I f.hom))
        (reducedKernelCoefficientEquiv G I hI B (Additive.ofMul x)) := by
  apply (Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
    (Additive (lieKernel G R)) C).injective
  change _ =
    (Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
      (Additive (lieKernel G R)) C)
      (TensorProduct.map
        (Langlands.CommutativeAlgebra.SquareZero.quotientTestMap I f.hom).toLinearMap
        LinearMap.id
        ((Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
          (Additive (lieKernel G R)) B).symm
          (flatKernelCoefficientEquiv G I hI B (Additive.ofMul x))))
  rw [Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv_naturality]
  change _ = TensorProduct.map f.hom.toLinearMap LinearMap.id
    ((Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
      (Additive (lieKernel G R)) B)
      ((Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
        (Additive (lieKernel G R)) B).symm
        (flatKernelCoefficientEquiv G I hI B (Additive.ofMul x))))
  rw [LinearEquiv.apply_symm_apply]
  change (Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
      (Additive (lieKernel G R)) C)
      ((Langlands.CommutativeAlgebra.SquareZero.reducedCoefficientEquiv I hI
        (Additive (lieKernel G R)) C).symm
        (flatKernelCoefficientEquiv G I hI C (Additive.ofMul y))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact flatKernelCoefficientEquiv_naturality G I hI f x y hxy

end Langlands.GroupScheme.Lie.SquareZero
