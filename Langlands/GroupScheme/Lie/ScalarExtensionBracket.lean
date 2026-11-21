import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.Lie.AffineBracketFunctoriality
import Mathlib.Algebra.Lie.BaseChange

/-! # Scalar extension of the actual tangent Lie algebra over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (A : Type u) [CommRing A] [Algebra k A]

/-- The published tangent Lie ring, for a `k`-algebra regarded as an algebra over
`CommRingCat.of k`. -/
local instance instKernelLieRingOfField (B : Type u) [CommRing B] [Algebra k B] :
    LieRing (Additive (lieKernel G B)) :=
  instAffineKernelLieRing (R := CommRingCat.of k) (A := B) G

/-- The published tangent Lie algebra, for a `k`-algebra regarded as an algebra
over `CommRingCat.of k`. -/
local instance instKernelLieAlgebraOfField (B : Type u) [CommRing B] [Algebra k B] :
    LieAlgebra B (Additive (lieKernel G B)) :=
  instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := B) G

/-- The scalar-extension isomorphism of actual tangent modules preserves the
actual tangent Lie bracket, for Mathlib's extended-scalars bracket on the source. -/
theorem kernelScalarExtension_lie (x y : A ⊗[k] Additive (lieKernel G k)) :
    kernelScalarExtension G A ⁅x, y⁆ =
      ⁅kernelScalarExtension G A x, kernelScalarExtension G A y⁆ := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    rw [show ⁅x₁ + x₂, y⁆ = ⁅x₁, y⁆ + ⁅x₂, y⁆ from add_lie x₁ x₂ y, map_add, h₁, h₂,
      map_add, add_lie]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      rw [show ⁅a ⊗ₜ[k] x, y₁ + y₂⁆ = ⁅a ⊗ₜ[k] x, y₁⁆ + ⁅a ⊗ₜ[k] x, y₂⁆ from
        lie_add (a ⊗ₜ[k] x) y₁ y₂, map_add, h₁, h₂, map_add, lie_add]
    | tmul b y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, kernelScalarExtension_tmul,
        kernelScalarExtension_tmul, kernelScalarExtension_tmul, lieKernelMapLinear_lie,
        smul_lie, lie_smul, smul_smul]

/-- Over a field, the actual tangent Lie algebra of an affine group locally of
finite type with coefficients in a commutative algebra `A` is the scalar
extension of the base tangent Lie algebra. -/
def kernelScalarExtensionLieEquiv :
    A ⊗[k] Additive (lieKernel G k) ≃ₗ⁅A⁆ Additive (lieKernel G A) :=
  { kernelScalarExtension G A with
    map_lie' := fun {x y} => kernelScalarExtension_lie G A x y }

@[simp] theorem kernelScalarExtensionLieEquiv_apply (x : A ⊗[k] Additive (lieKernel G k)) :
    kernelScalarExtensionLieEquiv G A x = kernelScalarExtension G A x := rfl

theorem kernelScalarExtensionLieEquiv_toLinearEquiv :
    (kernelScalarExtensionLieEquiv G A).toLinearEquiv = kernelScalarExtension G A := rfl

theorem kernelScalarExtensionLieEquiv_tmul (a : A) (x : Additive (lieKernel G k)) :
    kernelScalarExtensionLieEquiv G A (a ⊗ₜ x) =
      a • lieKernelMapLinear G (Algebra.ofId k A) x :=
  kernelScalarExtension_tmul G A a x

end Langlands.GroupScheme.Lie
