import Langlands.GroupScheme.Lie.AffineModule

/-! # The adjoint action on actual dual-number kernels -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A : Type u} [CommRing A] [Algebra R A]

/-- Constant-point conjugation is linear for actual epsilon scaling. -/
def lieKernelConjugationLinear [IsAffineHom G.X.hom] (g : Lie.AffinePoints G A) :
    Module.End A (Additive (lieKernel G A)) where
  toFun x := Additive.ofMul (lieKernelConjugation G g x.toMul)
  map_add' x y :=
    congrArg Additive.ofMul ((lieKernelConjugation G g).map_mul x.toMul y.toMul)
  map_smul' c x :=
    congrArg Additive.ofMul (lieKernelConjugation_scale G c g x.toMul).symm

@[simp] theorem lieKernelConjugationLinear_toMul [IsAffineHom G.X.hom]
    (g : Lie.AffinePoints G A) (x : Additive (lieKernel G A)) :
    (lieKernelConjugationLinear G g x).toMul = lieKernelConjugation G g x.toMul := rfl

/-- The adjoint representation on the actual dual-number identity kernel. -/
def adjoint (A : Type u) [CommRing A] [Algebra R A] [IsAffineHom G.X.hom] :
    Lie.AffinePoints G A →* Module.End A (Additive (lieKernel G A)) where
  toFun := lieKernelConjugationLinear G
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    change Lie.constant G 1 * x.toMul.val * (Lie.constant G 1)⁻¹ = x.toMul.val
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    change Lie.constant G (g * h) * x.toMul.val * (Lie.constant G (g * h))⁻¹ =
      Lie.constant G g * (Lie.constant G h * x.toMul.val * (Lie.constant G h)⁻¹) *
        (Lie.constant G g)⁻¹
    simp [mul_assoc]

@[simp] theorem adjoint_toMul [IsAffineHom G.X.hom]
    (g : Lie.AffinePoints G A) (x : Additive (lieKernel G A)) :
    (adjoint G A g x).toMul = lieKernelConjugation G g x.toMul := rfl

/-- The underlying actual-point formula for the adjoint action. -/
@[simp] theorem adjoint_val [IsAffineHom G.X.hom]
    (g : Lie.AffinePoints G A) (x : Additive (lieKernel G A)) :
    (adjoint G A g x).toMul.val =
      Lie.constant G g * x.toMul.val * (Lie.constant G g)⁻¹ := rfl

variable {B : Type u} [CommRing B] [Algebra R B]

/-- The adjoint action commutes with every change of test algebra. -/
theorem adjoint_naturality [IsAffineHom G.X.hom] (f : A →ₐ[R] B)
    (g : Lie.AffinePoints G A) (x : Additive (lieKernel G A)) :
    lieKernelMapLinear G f (adjoint G A g x) =
      adjoint G B (Lie.affineMap G f g) (lieKernelMapLinear G f x) :=
  congrArg Additive.ofMul (lieKernelConjugation_naturality G f g x.toMul)

end Langlands.GroupScheme
