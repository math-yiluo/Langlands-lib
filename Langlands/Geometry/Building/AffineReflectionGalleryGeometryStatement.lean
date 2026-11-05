import Langlands.Geometry.Building.AffineWeylGroups

/-! # Wall-reflection generation and galleries for locally finite arrangements -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA}
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- A locally finite real affine reflection arrangement with finite spanning
derivatives. Integrality and infinite parallel families are not required. -/
structure IsLocallyFiniteReflectionArrangement (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Prop where
  span_derivativeRoots_eq_top : Submodule.span ℝ (derivativeRoots Ψ) = ⊤
  linear_ne_zero : ∀ ψ ∈ Ψ, ψ.linear ≠ 0
  finite_derivativeRoots : (derivativeRoots Ψ).Finite
  exists_isCoroot : ∀ ψ ∈ Ψ, ∃ v : V, IsCoroot Ψ ψ v
  finite_bounded_at : ∀ (x : A) (bound : Module.Dual ℝ V → ℝ),
    {ψ | ψ ∈ Ψ ∧ |ψ x| ≤ bound ψ.linear}.Finite

/-- Separation of points by an actual generating affine reflection. Using the
reflection itself identifies proportional defining roots. -/
def reflectionSeparates (Ψ : Set (A →ᵃ[ℝ] ℝ)) (s : A ≃ᵃ[ℝ] A) (x y : A) : Prop :=
  ∃ ψ ∈ Ψ, ∃ (v : V) (hv : IsCoroot Ψ ψ v),
    s = affineReflection ψ hv.1 ∧ ψ x * ψ y < 0

/-- Reflections across a wall of the regular facet of `x`: this reflection is
exactly the reflection separating `x` from its image. -/
def wallReflections (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Set (A ≃ᵃ[ℝ] A) :=
  {s | reflectionSeparates Ψ s x (s x) ∧
    ∀ t, reflectionSeparates Ψ t x (s x) → t = s}

end AffineRootSystem

/-- The geometric gallery prerequisite: reflections across the walls of a
regular facet generate the actual reflection group, and this subgroup
transports that facet to every regular facet. -/
def AffineReflectionGalleryGeometryStatement : Prop :=
  ∀ (V : Type uV) (A : Type uA) [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    (Ψ : Set (A →ᵃ[ℝ] ℝ)),
    AffineRootSystem.IsLocallyFiniteReflectionArrangement Ψ →
      ∀ x : A, (∀ ψ ∈ Ψ, ψ x ≠ 0) →
        Subgroup.closure (AffineRootSystem.wallReflections Ψ x) =
          AffineRootSystem.affineWeylGroup Ψ ∧
        ∀ y : A, (∀ ψ ∈ Ψ, ψ y ≠ 0) →
          ∃ w : Subgroup.closure (AffineRootSystem.wallReflections Ψ x),
            AffineRootSystem.facetRel Ψ ((w : A ≃ᵃ[ℝ] A) x) y

end Langlands.Geometry.Building
