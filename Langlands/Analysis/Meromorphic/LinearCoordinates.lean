import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Holomorphy and meromorphy in linear coordinates

Holomorphic and meromorphic functions on a finite-dimensional complex vector
space that carries no chosen topology, such as the parameter space
`X^*(M) ⊗ ℂ` of Bernstein–Lapid §2.1: the notions of
`Langlands.Analysis.Meromorphic.AnalyticSystems` are required in every complex
linear coordinate system `ℂⁿ ≃ X`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open scoped Manifold

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- A function `f : X → V` on a complex vector space is holomorphic on `U` in
linear coordinates when `X` is finite-dimensional and, for every complex linear
isomorphism `e : ℂⁿ ≃ X`, the function `f ∘ e` is holomorphic on `e ⁻¹' U`. -/
def IsHolomorphicInCoordinatesOn (f : X → V) (U : Set X) : Prop :=
  FiniteDimensional ℂ X ∧ ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X),
    IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (f ∘ e) (e ⁻¹' U)

/-- A function `f : X → V` on a complex vector space is meromorphic on `X` with
domain of holomorphy `U` in linear coordinates when `X` is finite-dimensional
and, for every complex linear isomorphism `e : ℂⁿ ≃ X`, the function `f ∘ e`
is meromorphic on `ℂⁿ` with domain of holomorphy `e ⁻¹' U`. -/
def IsMeromorphicInCoordinatesOn (f : X → V) (U : Set X) : Prop :=
  FiniteDimensional ℂ X ∧ ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X),
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (f ∘ e) (e ⁻¹' U)

end Langlands.Analysis.Meromorphic
