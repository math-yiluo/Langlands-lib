import Langlands.Global.Factors.FiniteComparisonStatement
import Langlands.Global.Arithmetic.CharacterPrescriptionStatement
import Mathlib.Data.Finset.Sum

/-!
# Conditional comparison using actual Hecke twists

Both twists are chosen before the common exceptional set is enlarged. Every
infinite place and every auxiliary finite place remains in the comparison.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u

namespace Langlands.Global.FunctionalEquationComparison

variable (K : Type u) [Field K] [NumberField K]

/-- All actual places, with the two kinds kept distinct. -/
abbrev AllPlaces := InfinitePlace K ⊕ FinitePlace K

/-- The entire archimedean block. -/
def archimedeanBlock : Finset (AllPlaces K) := by
  classical
  exact Finset.univ.disjSum ∅

/-- One finite exceptional set containing every infinite place. -/
def exceptionalPlaces (T : Finset (FinitePlace K)) : Finset (AllPlaces K) := by
  classical
  exact Finset.univ.disjSum T

/-- The local factors depend only on the character. Partial Euler tails also
depend on the finite set omitted from their products. -/
structure HeckeEulerFamily where
  localFactors : HeckeCharacter K → AllPlaces K → LocalFactors
  partialL : HeckeCharacter K → Finset (FinitePlace K) → ℂ → ℂ
  partialDualL : HeckeCharacter K → Finset (FinitePlace K) → ℂ → ℂ

/-- Specialize the partial tails to one common finite exceptional set without
changing any local factor. Analytic properties are separate inputs. -/
def HeckeEulerFamily.eulerData {K : Type u} [Field K] [NumberField K]
    (D : HeckeEulerFamily K) (χ : HeckeCharacter K)
    (B : Finset (FinitePlace K)) : FiniteEulerData (AllPlaces K) where
  localFactors := D.localFactors χ
  partialL := D.partialL χ B
  partialDualL := D.partialDualL χ B

/-- The actual character requirements used for the two successive twists.
The first is deep at every original bad finite place; the second is trivial at
w and deep at every other original bad finite place. -/
def TwoHeckeTwists (T : Finset (FinitePlace K)) (w : FinitePlace K)
    (r : FinitePlace K → ℕ) (χ₁ χ₂ : HeckeCharacter K) : Prop :=
  χ₁.HasFiniteOrder ∧ χ₂.HasFiniteOrder ∧
    χ₁.HasPrescribedInfinityComponent 1 ∧ χ₂.HasPrescribedInfinityComponent 1 ∧
    χ₂.finiteComponent w = 1 ∧
    (∀ v ∈ T, NontrivialOnPrincipalUnits v (χ₁.finiteComponent v) (r v)) ∧
    (∀ v ∈ T, v ≠ w → NontrivialOnPrincipalUnits v (χ₂.finiteComponent v) (r v))

/-- The analytic/global input, with a single finite enlargement chosen after
both characters. All four nonzero meromorphic factor families, all four full
functional equations, and both outside-set Euler-product comparisons are
separate hypotheses. No gamma comparison is part of this predicate. -/
def CommonTwistEulerInputs (T : Finset (FinitePlace K))
    (D E : HeckeEulerFamily K) : Prop := by
  classical
  exact ∀ (χ₁ χ₂ : HeckeCharacter K), χ₁.HasFiniteOrder → χ₂.HasFiniteOrder →
    χ₁.HasPrescribedInfinityComponent 1 → χ₂.HasPrescribedInfinityComponent 1 →
    ∃ B : Finset (FinitePlace K), T ⊆ B ∧
      (∀ v ∉ B, χ₁.IsUnramifiedAt v ∧ χ₂.IsUnramifiedAt v) ∧
      Admissible (D.eulerData χ₁ B) (exceptionalPlaces K B) ∧
      Admissible (E.eulerData χ₁ B) (exceptionalPlaces K B) ∧
      Admissible (D.eulerData χ₂ B) (exceptionalPlaces K B) ∧
      Admissible (E.eulerData χ₂ B) (exceptionalPlaces K B) ∧
      FunctionalEquation (D.eulerData χ₁ B) (exceptionalPlaces K B) ∧
      FunctionalEquation (E.eulerData χ₁ B) (exceptionalPlaces K B) ∧
      FunctionalEquation (D.eulerData χ₂ B) (exceptionalPlaces K B) ∧
      FunctionalEquation (E.eulerData χ₂ B) (exceptionalPlaces K B) ∧
      ∃ σ₁ σ₂ : ℝ,
        HasEulerProductsOutside (D.eulerData χ₁ B) (exceptionalPlaces K B) σ₁ ∧
        HasEulerProductsOutside (E.eulerData χ₁ B) (exceptionalPlaces K B) σ₁ ∧
        MatchesOutside (D.eulerData χ₁ B) (E.eulerData χ₁ B)
          (exceptionalPlaces K B) σ₁ ∧
        HasEulerProductsOutside (D.eulerData χ₂ B) (exceptionalPlaces K B) σ₂ ∧
        HasEulerProductsOutside (E.eulerData χ₂ B) (exceptionalPlaces K B) σ₂ ∧
        MatchesOutside (D.eulerData χ₂ B) (E.eulerData χ₂ B)
          (exceptionalPlaces K B) σ₂

/-- Triviality on the whole archimedean factor preserves each side separately. -/
def InfinityGammaPreservation
    (D E : HeckeEulerFamily K) : Prop :=
  ∀ χ : HeckeCharacter K, χ.HasFiniteOrder →
    χ.HasPrescribedInfinityComponent 1 → ∀ v : InfinitePlace K,
    MeromorphicEq (D.localFactors χ (.inl v)).gamma
      (D.localFactors 1 (.inl v)).gamma ∧
    MeromorphicEq (E.localFactors χ (.inl v)).gamma
      (E.localFactors 1 (.inl v)).gamma

/-- Triviality at the selected finite place preserves each side separately. -/
def FiniteGammaPreservation (w : FinitePlace K)
    (D E : HeckeEulerFamily K) : Prop :=
  ∀ χ : HeckeCharacter K, χ.HasFiniteOrder → χ.finiteComponent w = 1 →
    MeromorphicEq (D.localFactors χ (.inr w)).gamma
      (D.localFactors 1 (.inr w)).gamma ∧
    MeromorphicEq (E.localFactors χ (.inr w)).gamma
      (E.localFactors 1 (.inr w)).gamma

/-- At every original bad finite place the supplied depth ensures stability. -/
def RamifiedGammaStability (T : Finset (FinitePlace K)) (r : FinitePlace K → ℕ)
    (D E : HeckeEulerFamily K) : Prop :=
  ∀ v ∈ T, ∀ χ : HeckeCharacter K, χ.HasFiniteOrder →
    NontrivialOnPrincipalUnits v (χ.finiteComponent v) (r v) →
    MeromorphicEq (D.localFactors χ (.inr v)).gamma
      (E.localFactors χ (.inr v)).gamma

/-- Stability away from the original bad set, including any new ramification
of a chosen finite-order twist. -/
def OutsideGammaStability (T : Finset (FinitePlace K))
    (D E : HeckeEulerFamily K) : Prop :=
  ∀ χ : HeckeCharacter K, χ.HasFiniteOrder → ∀ v ∉ T,
    MeromorphicEq (D.localFactors χ (.inr v)).gamma
      (E.localFactors χ (.inr v)).gamma

/-- A conditional actual-character adapter to the generic two-twist engine.
The families must be linked to actual arithmetic and automorphic factors by a
separate certificate adapter. This target proves no character prescription,
global functional equation, factor existence or local stability theorem. -/
def HeckeTwistComparisonStatement : Prop :=
  RamifiedTwistIsolationStatement.{u} →
  ∀ (K : Type u) [Field K] [NumberField K]
    (T : Finset (FinitePlace K)) (w : FinitePlace K), w ∈ T →
  ∀ (r : FinitePlace K → ℕ)
    (D E : HeckeEulerFamily K),
    CommonTwistEulerInputs K T D E →
    InfinityGammaPreservation K D E →
    FiniteGammaPreservation K w D E →
    RamifiedGammaStability K T r D E →
    OutsideGammaStability K T D E →
    ∃ (χ₁ χ₂ : HeckeCharacter K) (B : Finset (FinitePlace K)),
      TwoHeckeTwists K T w r χ₁ χ₂ ∧ T ⊆ B ∧
      (∀ v ∉ B, χ₁.IsUnramifiedAt v ∧ χ₂.IsUnramifiedAt v) ∧
      MeromorphicEq (fun s => ∏ v ∈ archimedeanBlock K,
        (D.localFactors 1 v).gamma s)
        (fun s => ∏ v ∈ archimedeanBlock K, (E.localFactors 1 v).gamma s) ∧
      MeromorphicEq (D.localFactors 1 (.inr w)).gamma
        (E.localFactors 1 (.inr w)).gamma

end Langlands.Global.FunctionalEquationComparison
