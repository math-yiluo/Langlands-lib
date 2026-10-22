import Langlands.LocalFactor.Ramification.Descent
import Langlands.Representation.Twist.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite-Galois Artin and Swan conductor statements

The conductors are the published rational sums for the actual valuation-ring
action of a finite p-adic Galois extension. All statements retain the Galois
hypothesis and use finite-dimensional complex representations.
-/

namespace Langlands.Ramification.Padic

universe uK uL uU uV uW

section Components

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  {U : Type uU} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Each actual rational conductor equals a natural number. -/
def FiniteGaloisConductorIntegralityStatement : Prop :=
  ∀ [IsGalois K F.Carrier]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V),
    (∃ a : ℕ, artinConductor T K ρ = (a : ℚ)) ∧
    (∃ s : ℕ, swanConductor T K ρ = (s : ℚ))

/-- Additivity for actual short exact sequences of complex representations. -/
def FiniteGaloisConductorExactSequenceStatement : Prop :=
  ∀ [IsGalois K F.Carrier]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) U)
    (σ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (τ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W)
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ),
    Function.Injective i →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    Function.Surjective q →
    artinConductor T K σ = artinConductor T K ρ + artinConductor T K τ ∧
    swanConductor T K σ = swanConductor T K ρ + swanConductor T K τ

/-- The binary direct sum, realized by the product vector space and action. -/
def FiniteGaloisConductorDirectSumStatement : Prop :=
  ∀ [IsGalois K F.Carrier]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (σ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W),
    artinConductor T K (ρ.prod σ) = artinConductor T K ρ + artinConductor T K σ ∧
    swanConductor T K (ρ.prod σ) = swanConductor T K ρ + swanConductor T K σ

/-- Invariance under the inverse-element action on the actual algebraic dual. -/
def FiniteGaloisConductorDualStatement : Prop :=
  ∀ [IsGalois K F.Carrier]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V),
    artinConductor T K ρ.dual = artinConductor T K ρ ∧
    swanConductor T K ρ.dual = swanConductor T K ρ

/-- Scalar twisting by a genuine one-dimensional character trivial on inertia. -/
def FiniteGaloisConductorUnramifiedTwistStatement : Prop :=
  ∀ [IsGalois K F.Carrier]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ),
    (∀ g ∈ inertia T K, χ g = 1) →
    artinConductor T K (Langlands.twist χ ρ) = artinConductor T K ρ ∧
    swanConductor T K (Langlands.twist χ ρ) = swanConductor T K ρ

/-- Vanishing detects trivial action of actual inertia and of the first lower group. -/
def FiniteGaloisConductorVanishingStatement : Prop :=
  ∀ [IsGalois K F.Carrier]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V),
    (artinConductor T K ρ = 0 ↔
      ∀ g ∈ inertia T K, ∀ v : V, ρ g v = v) ∧
    (swanConductor T K ρ = 0 ↔
      ∀ g ∈ lowerRamificationGroup T K 1, ∀ v : V, ρ g v = v)

/-- The tame consequence of the published tame-plus-Swan decomposition. -/
def FiniteGaloisTameArtinStatement : Prop :=
  ∀ [IsGalois K F.Carrier]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V),
    (∀ g ∈ lowerRamificationGroup T K 1, ∀ v : V, ρ g v = v) →
    artinConductor T K ρ =
      (fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) : ℚ)

end Components

/-- The complete family, with arbitrary prime, compatible p-adic field data,
intermediate base field, and three independently universed representation spaces.
Each component explicitly quantifies its finite-Galois hypothesis. -/
def FiniteGaloisConductorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uL} p)
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    (U : Type uU) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W],
    FiniteGaloisConductorIntegralityStatement T K (V := V) ∧
    FiniteGaloisConductorExactSequenceStatement T K (U := U) (V := V) (W := W) ∧
    FiniteGaloisConductorDirectSumStatement T K (V := V) (W := W) ∧
    FiniteGaloisConductorDualStatement T K (V := V) ∧
    FiniteGaloisConductorUnramifiedTwistStatement T K (V := V) ∧
    FiniteGaloisConductorVanishingStatement T K (V := V) ∧
    FiniteGaloisTameArtinStatement T K (V := V)

end Langlands.Ramification.Padic
