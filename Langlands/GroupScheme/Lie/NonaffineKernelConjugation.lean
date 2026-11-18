import Langlands.GroupScheme.Lie.NonaffineKernel

/-! # Actual linear conjugation representations on nonaffine square-zero kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie.NonaffineKernel

open Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A : Type u} [CommRing A] [Algebra R A] (J : Ideal A) [Fact (SqZero J)]

/-- Evaluation of the supplied linear conjugation on underlying actual points. -/
@[simp]
theorem kernelConjugationLinear_val (g : AffinePoints G A) (x : Additive (kernel G J)) :
    (kernelConjugationLinear G J g x).toMul.val = g * x.toMul.val * g⁻¹ :=
  congrArg Subtype.val (kernelConjugationLinear_apply G J g x)

/-- The identity point induces the identity linear endomorphism. -/
theorem kernelConjugationLinear_one :
    kernelConjugationLinear G J (1 : AffinePoints G A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [kernelConjugationLinear_val, one_mul, inv_one, mul_one, LinearMap.id_apply]

/-- Multiplication of acting points is composition of the actual linear
conjugation endomorphisms. -/
theorem kernelConjugationLinear_mul (g h : AffinePoints G A) :
    kernelConjugationLinear G J (g * h) =
      (kernelConjugationLinear G J g).comp (kernelConjugationLinear G J h) := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  change (kernelConjugationLinear G J (g * h) x).toMul.val =
    (kernelConjugationLinear G J g (kernelConjugationLinear G J h x)).toMul.val
  rw [kernelConjugationLinear_val, kernelConjugationLinear_val,
    kernelConjugationLinear_val]
  group

/-- Actual point conjugation is a representation by linear endomorphisms of
the full square-zero reduction kernel. -/
def kernelConjugationEnd : AffinePoints G A →* Module.End A (Additive (kernel G J)) where
  toFun := kernelConjugationLinear G J
  map_one' := kernelConjugationLinear_one G J
  map_mul' := kernelConjugationLinear_mul G J

/-- Conjugation gives an actual homomorphism into linear automorphisms,
without any affine, separated or smooth target hypothesis. -/
def kernelConjugationAut :
    AffinePoints G A →* (Additive (kernel G J) ≃ₗ[A] Additive (kernel G J)) where
  toFun g := LinearEquiv.ofLinearMap (kernelConjugationEnd G J g)
    (kernelConjugationEnd G J g⁻¹)
    (by change kernelConjugationEnd G J g * kernelConjugationEnd G J g⁻¹ = 1
        rw [← map_mul, mul_inv_cancel, map_one])
    (by change kernelConjugationEnd G J g⁻¹ * kernelConjugationEnd G J g = 1
        rw [← map_mul, inv_mul_cancel, map_one])
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change kernelConjugationEnd G J 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change kernelConjugationEnd G J (g * h) x =
      kernelConjugationEnd G J g (kernelConjugationEnd G J h x)
    rw [map_mul]
    rfl

/-- The constructed automorphism retains the original actual conjugation. -/
@[simp]
theorem kernelConjugationAut_val (g : AffinePoints G A) (x : Additive (kernel G J)) :
    (kernelConjugationAut G J g x).toMul.val = g * x.toMul.val * g⁻¹ :=
  kernelConjugationLinear_val G J g x

/-- The full linear automorphism depends only on the reducing acting point. -/
theorem kernelConjugationAut_eq_of_reduction_eq (g g' : AffinePoints G A)
    (h : reduction G J g = reduction G J g') :
    kernelConjugationAut G J g = kernelConjugationAut G J g' := by
  apply LinearEquiv.ext
  intro x
  change kernelConjugationLinear G J g x = kernelConjugationLinear G J g' x
  rw [kernelConjugationLinear_eq_of_reduction_eq G J g g' h]

end Langlands.GroupScheme.Lie.NonaffineKernel
