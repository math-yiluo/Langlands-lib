import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Coefficients, smooth endomorphisms and the formal degree (Renard IV.1.4)

For an admissible representation `W`, the map `W ⊗ W̃ → End(W)`, `w ⊗ λ ↦ λ(·) w`, is
injective with image the smooth endomorphisms (IV.1.4.1). For an irreducible representation
`τ` of a unimodular t.d. group with compactly supported coefficients, the functions
`ˇφ_{w,λ} : g ↦ λ(τ(g⁻¹) w)` lie in the Hecke algebra, act by zero on every irreducible
representation not isomorphic to `τ`, and act on `τ` as `κ(τ) λ(·) w` for a nonzero scalar
`κ(τ)`, the inverse of the formal degree (IV.1.4, Proposition). For a compact group with
Haar probability measure, `κ(τ)⁻¹` is the dimension of `τ` (IV.1.4, Remark 2).
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.4, (IV.1.4.1) and the remark after its proof: for an admissible smooth
representation `τ` of a Hausdorff, locally compact, totally disconnected group `G`, the linear
map `α : W ⊗ W̃ → End(W)`, `α(w ⊗ λ)(v) = λ(v) w`, from the tensor product of `W` with its
smooth dual, is injective, and its image is the space `End(W)₀` of smooth endomorphisms: the
`A` with `τ(k₁) A τ(k₂) = A` for all `k₁, k₂` in some open subgroup. -/
def SmoothEndomorphismTensorStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (τ : SmoothRep.{0, u, v} ℂ G), τ.IsAdmissible →
    let α : TensorProduct ℂ τ (SmoothDual τ.representation) →ₗ[ℂ] Module.End ℂ τ :=
      TensorProduct.lift
        ((LinearMap.smulRightₗ (R := ℂ) (M := τ) (M₂ := τ)).flip.compl₂
          (smoothVectors τ.representation.dual).subtype)
    Function.Injective α ∧
      Set.range α =
        {A : Module.End ℂ τ | ∃ K : OpenSubgroup G, ∀ k₁ ∈ K, ∀ k₂ ∈ K,
          τ.representation k₁ * A * τ.representation k₂ = A}

/-- Renard IV.1.4, Proposition and the definition of the formal degree: let `G` be a
Hausdorff, locally compact, totally disconnected group, countable at infinity, with a regular
Haar measure `μ` that is also right invariant, and `τ` an irreducible smooth representation
with compactly supported smooth coefficients. Say that `f ∈ H(G)` is the coefficient
`ˇφ_{w,λ}` if `f(g) = λ(τ(g⁻¹) w)` for all `g`. Then

* every `ˇφ_{w,λ}`, for `w ∈ τ` and `λ` in the smooth dual, lies in `H(G)`;
* (i) `ρ(ˇφ_{w,λ}) = 0` for every irreducible smooth `ρ` not isomorphic to `τ`;
* (ii) there is a nonzero scalar `κ(τ)` with `τ(ˇφ_{w,λ}) x = κ(τ) λ(x) w` for all `w`, `λ`
  and `x`. Its inverse `d(τ) = κ(τ)⁻¹` is the formal degree of `τ` for `μ`. -/
def CompactCoefficientFormalDegreeStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant] (τ : SmoothRep.{0, u, v} ℂ G),
    τ.IsIrreducible → HasCompactSmoothDualCoefficients τ.representation →
    let IsCoefficient : τ → SmoothDual τ.representation → Hecke.HeckeAlgebra μ → Prop :=
      fun w ℓ f => ∀ g : G, f g = (ℓ : Module.Dual ℂ τ) (τ.representation g⁻¹ w)
    (∀ (w : τ) (ℓ : SmoothDual τ.representation), ∃ f, IsCoefficient w ℓ f) ∧
    (∀ ρ : SmoothRep.{0, u, v} ℂ G, ρ.IsIrreducible → IsEmpty (ρ ≅ τ) →
      ∀ (w : τ) (ℓ : SmoothDual τ.representation) (f : Hecke.HeckeAlgebra μ),
        IsCoefficient w ℓ f → Hecke.heckeAction μ ρ.representation ρ.isSmooth f = 0) ∧
    ∃ κ : ℂ, κ ≠ 0 ∧
      ∀ (w : τ) (ℓ : SmoothDual τ.representation) (f : Hecke.HeckeAlgebra μ),
        IsCoefficient w ℓ f → ∀ x : τ,
          Hecke.heckeAction μ τ.representation τ.isSmooth f x =
            (κ * (ℓ : Module.Dual ℂ τ) x) • w

/-- Renard IV.1.4, Remark 2: let `G` be a compact Hausdorff totally disconnected group with
its Haar probability measure `μ`, and `τ` an irreducible smooth representation. Then `τ` is
finite-dimensional, and for every coefficient `f(g) = λ(τ(g⁻¹) w)` one has
`τ(f) x = (dim τ)⁻¹ λ(x) w`; that is, the scalar `κ(τ)` of the preceding statement is
`(dim τ)⁻¹`, and the formal degree of `τ` is its dimension. -/
def CompactGroupFormalDegreeStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (τ : SmoothRep.{0, u, v} ℂ G), μ Set.univ = 1 → τ.IsIrreducible →
    FiniteDimensional ℂ τ ∧
      ∀ (w : τ) (ℓ : SmoothDual τ.representation) (f : Hecke.HeckeAlgebra μ),
        (∀ g : G, f g = (ℓ : Module.Dual ℂ τ) (τ.representation g⁻¹ w)) → ∀ x : τ,
          Hecke.heckeAction μ τ.representation τ.isSmooth f x =
            ((Module.finrank ℂ τ : ℂ)⁻¹ * (ℓ : Module.Dual ℂ τ) x) • w

/-- The three statements above. -/
def CompactFormalDegreeStatements.{u', v'} : Prop :=
  SmoothEndomorphismTensorStatement.{u', v'} ∧
    CompactCoefficientFormalDegreeStatement.{u', v'} ∧
    CompactGroupFormalDegreeStatement.{u', v'}

end Langlands.Renard.CompactRepresentation
