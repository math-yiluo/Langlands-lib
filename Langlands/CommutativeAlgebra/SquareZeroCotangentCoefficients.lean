import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor
import Mathlib.RingTheory.Ideal.Cotangent

/-! # Quotient-base coefficients of a square-zero ideal -/

noncomputable section

universe u

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.CommutativeAlgebra.SquareZero

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)

/-- For a square-zero ideal the canonical cotangent quotient changes no
underlying module elements and supplies the canonical quotient-base action. -/
def idealCotangentEquiv : I ≃ₗ[R] I.Cotangent :=
  LinearEquiv.ofBijective I.toCotangent ⟨by
    intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hxy := I.toCotangent_eq.mp h
    simpa only [hI, Ideal.mem_bot] using hxy,
    I.toCotangent_surjective⟩

@[simp]
theorem idealCotangentEquiv_apply (i : I) :
    idealCotangentEquiv I hI i = I.toCotangent i := rfl

variable (L : Type u) [AddCommGroup L] [Module R L]
variable (B : Type u) [CommRing B] [Algebra R B]

local instance quotientTestRightAlgebra : Algebra B ((R ⧸ I) ⊗[R] B) :=
  Algebra.TensorProduct.rightAlgebra

/-- Tensor the coefficient over the quotient base on the actual fibre algebra,
then identify it with the original base ideal coefficient tensor. -/
def reducedCoefficientEquiv :
    (((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] (I.Cotangent ⊗[R] L)) ≃ₗ[B]
      (B ⊗[R] (I ⊗[R] L)) :=
  Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.coefficientTensorEquiv.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (TensorProduct.congr (idealCotangentEquiv I hI).symm (LinearEquiv.refl R L)))

/-- The comparison on tensors obtained from an actual base ideal element. -/
theorem reducedCoefficientEquiv_one_tmul (b : B) (i : I) (x : L) :
    reducedCoefficientEquiv I hI L B
      (((1 : R ⧸ I) ⊗ₜ[R] b) ⊗ₜ[R ⧸ I] (I.toCotangent i ⊗ₜ[R] x)) =
      b ⊗ₜ[R] (i ⊗ₜ[R] x) := by
  change (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (TensorProduct.congr (idealCotangentEquiv I hI).symm (LinearEquiv.refl R L)))
      (b ⊗ₜ[R] ((1 : R ⧸ I) • (I.toCotangent i ⊗ₜ[R] x))) = _
  rw [one_smul, TensorProduct.AlgebraTensorModule.congr_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.refl_apply,
    ← idealCotangentEquiv_apply I hI, LinearEquiv.symm_apply_apply]

/-- The inverse comparison has the canonical quotient-base pure tensor formula. -/
theorem reducedCoefficientEquiv_symm_tmul (b : B) (i : I) (x : L) :
    (reducedCoefficientEquiv I hI L B).symm (b ⊗ₜ[R] (i ⊗ₜ[R] x)) =
      (((1 : R ⧸ I) ⊗ₜ[R] b) ⊗ₜ[R ⧸ I] (I.toCotangent i ⊗ₜ[R] x)) := by
  apply (reducedCoefficientEquiv I hI L B).injective
  rw [LinearEquiv.apply_symm_apply, reducedCoefficientEquiv_one_tmul]

variable {B} {C : Type u} [CommRing C] [Algebra R C]

/-- Extension of an algebra morphism to the actual quotient-base test algebra. -/
def quotientTestMap (f : B →ₐ[R] C) :
    ((R ⧸ I) ⊗[R] B) →ₐ[R ⧸ I] ((R ⧸ I) ⊗[R] C) :=
  Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I)) f

@[simp]
theorem quotientTestMap_tmul (f : B →ₐ[R] C) (c : R ⧸ I) (b : B) :
    quotientTestMap I f (c ⊗ₜ[R] b) = c ⊗ₜ[R] f b := rfl

/-- The quotient-base coefficient comparison is natural in every coefficient
algebra morphism; no flatness is needed for this tensor rearrangement. -/
theorem reducedCoefficientEquiv_naturality (f : B →ₐ[R] C)
    (z : ((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] (I.Cotangent ⊗[R] L)) :
    reducedCoefficientEquiv I hI L C
      (TensorProduct.map (quotientTestMap I f).toLinearMap LinearMap.id z) =
      TensorProduct.map f.toLinearMap LinearMap.id
        (reducedCoefficientEquiv I hI L B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul t m =>
    induction t using TensorProduct.inductionOn with
    | tmul c b =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, quotientTestMap_tmul,
        LinearMap.id_apply, reducedCoefficientEquiv, LinearEquiv.trans_apply,
        Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.coefficientTensorEquiv_tmul,
        TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
    | add t s ht hs =>
      simp only [TensorProduct.add_tmul, map_add, ht, hs]
  | add z w hz hw => simp only [map_add, hz, hw]

end Langlands.CommutativeAlgebra.SquareZero
