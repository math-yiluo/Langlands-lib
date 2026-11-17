import Langlands.GroupScheme.AffinePoints
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Regular low-degree cochains with quasi-coherent module coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}}
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Points of the quasi-coherent additive module functor associated to `M`
on an affine test algebra. No finite generation or projectivity is assumed. -/
abbrev ModulePoints (A : CommAlgCat.{u} R) := A ⊗[R] M

/-- Extension of coefficients in a quasi-coherent module functor. -/
def modulePointMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    ModulePoints M A →ₗ[R] ModulePoints M B :=
  TensorProduct.map f.hom.toLinearMap LinearMap.id

@[simp]
theorem modulePointMap_tmul {A B : CommAlgCat.{u} R} (f : A ⟶ B) (a : A) (m : M) :
    modulePointMap M f (a ⊗ₜ[R] m) = f.hom a ⊗ₜ[R] m := rfl

@[simp]
theorem modulePointMap_id (A : CommAlgCat.{u} R) :
    modulePointMap M (𝟙 A) = LinearMap.id := by
  ext a m
  rfl

theorem modulePointMap_comp {A B C : CommAlgCat.{u} R} (f : A ⟶ B) (g : B ⟶ C) :
    modulePointMap M (f ≫ g) = (modulePointMap M g).comp (modulePointMap M f) := by
  ext a m
  rfl

variable (H : GroupScheme (Spec R))

/-- An action of the actual affine-point functor of `H` on the quasi-coherent
module functor `A ↦ A ⊗ M`, linear over each test algebra and natural in it. -/
structure ModuleRepresentation where
  action (A : CommAlgCat.{u} R) :
    H.affinePoints A →* (ModulePoints M A ≃ₗ[A] ModulePoints M A)
  naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h : H.affinePoints A) (m : ModulePoints M A) :
    modulePointMap M f (action A h m) =
      action B (H.affinePointMap f h) (modulePointMap M f m)

/-- A regular one-cochain is a family natural in all affine test algebras. -/
structure OneCochain where
  value (A : CommAlgCat.{u} R) : H.affinePoints A → ModulePoints M A
  naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B) (h : H.affinePoints A) :
    modulePointMap M f (value A h) = value B (H.affinePointMap f h)

/-- A regular two-cochain is natural in pairs of points on all affine tests. -/
structure TwoCochain where
  value (A : CommAlgCat.{u} R) :
    H.affinePoints A → H.affinePoints A → ModulePoints M A
  naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B) (h k : H.affinePoints A) :
    modulePointMap M f (value A h k) =
      value B (H.affinePointMap f h) (H.affinePointMap f k)

variable {H M}

/-- The inhomogeneous one-cocycle equation. -/
def OneCochain.IsCocycle (c : OneCochain M H) (ρ : ModuleRepresentation M H) : Prop :=
  ∀ (A : CommAlgCat.{u} R) (h k : H.affinePoints A),
    c.value A (h * k) = c.value A h + ρ.action A h (c.value A k)

/-- A regular one-cocycle is a coboundary if it is obtained from an actual
base-module element by the given action. -/
def OneCochain.IsCoboundary (c : OneCochain M H)
    (ρ : ModuleRepresentation M H) : Prop :=
  ∃ m : M, ∀ (A : CommAlgCat.{u} R) (h : H.affinePoints A),
    c.value A h = ρ.action A h ((1 : A) ⊗ₜ[R] m) - (1 : A) ⊗ₜ[R] m

/-- The inhomogeneous Hochschild two-cocycle equation. -/
def TwoCochain.IsCocycle (c : TwoCochain M H) (ρ : ModuleRepresentation M H) : Prop :=
  ∀ (A : CommAlgCat.{u} R) (h k l : H.affinePoints A),
    c.value A h k + c.value A (h * k) l =
      ρ.action A h (c.value A k l) + c.value A h (k * l)

/-- A regular two-cocycle is a coboundary of a natural one-cochain. -/
def TwoCochain.IsCoboundary (c : TwoCochain M H)
    (ρ : ModuleRepresentation M H) : Prop :=
  ∃ b : OneCochain M H, ∀ (A : CommAlgCat.{u} R) (h k : H.affinePoints A),
    c.value A h k + b.value A (h * k) =
      ρ.action A h (b.value A k) + b.value A h

/-- Vanishing in the two positive degrees used by homomorphism deformation,
expressed as contraction of actual natural cochains. -/
def HasVanishingLowDegreeCohomology (H : GroupScheme (Spec R)) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M] (ρ : ModuleRepresentation M H),
    (∀ c : OneCochain M H, c.IsCocycle ρ → c.IsCoboundary ρ) ∧
    (∀ c : TwoCochain M H, c.IsCocycle ρ → c.IsCoboundary ρ)

end Langlands.GroupScheme.Cohomology
