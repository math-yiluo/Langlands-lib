import Langlands.Automorphic.Forms
import Langlands.Automorphic.DifferentialCenterFinite

/-! # Preservation obligations for actual automorphic forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The genuine enveloping differential of an actual automorphic form is finite
under the standard infinite compact subgroup. -/
def AutomorphicDifferentialInfiniteFiniteStatement : Prop :=
  ∀ (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : AutomorphicForms K n),
    IsInfiniteFinite K n (standardInfiniteCompact K n)
      (finiteSmoothEnvelopingAction K n a f.val).val

/-- The genuine enveloping differential of an actual automorphic form has
polynomial growth separately on every finite slice. -/
def AutomorphicDifferentialGrowthStatement : Prop :=
  ∀ (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : AutomorphicForms K n),
    HasPolynomialGrowth K n (finiteSmoothEnvelopingAction K n a f.val).val

/-- The actual automorphic subspace is stable under every genuine enveloping
operator on the finite-smooth ambient space. -/
def AutomorphicDifferentialPreservationStatement : Prop :=
  ∀ (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : FiniteSmoothRationalFunctions K n),
    f ∈ automorphicSubrepresentation K n →
      finiteSmoothEnvelopingAction K n a f ∈ automorphicSubrepresentation K n

/-- Smooth right translation by each element of the standard infinite compact
subgroup preserves the actual automorphic predicate. -/
def AutomorphicCompactTranslationStatement : Prop :=
  ∀ (k : standardInfiniteCompact K n) (f : SmoothRationalFunctions K n),
    IsAutomorphicForm K n f →
      IsAutomorphicForm K n
        (smoothRightAction K n (AdelicGL.ofInfinite K n k.val) f)

/-- The coherent group of differential and compact-translation obligations. -/
def AutomorphicPreservationStatement : Prop :=
  AutomorphicDifferentialInfiniteFiniteStatement K n ∧
    AutomorphicDifferentialGrowthStatement K n ∧
    AutomorphicDifferentialPreservationStatement K n ∧
    AutomorphicCompactTranslationStatement K n

/-- Finite level and simultaneous center finiteness are already preserved, so
the remaining differential conditions are precisely compact finiteness and growth. -/
theorem automorphicDifferentialPreservation_iff :
    AutomorphicDifferentialPreservationStatement K n ↔
      AutomorphicDifferentialInfiniteFiniteStatement K n ∧
        AutomorphicDifferentialGrowthStatement K n := by
  constructor
  · intro h
    constructor
    · intro a f
      exact ((mem_automorphicSubrepresentation K n _).mp (h a f.val f.property)).2.1
    · intro a f
      exact ((mem_automorphicSubrepresentation K n _).mp (h a f.val f.property)).2.2.2
  · rintro ⟨hk, hg⟩ a f hf
    have h := (mem_automorphicSubrepresentation K n f).mp hf
    apply (mem_automorphicSubrepresentation K n _).mpr
    exact ⟨finiteSmoothEnvelopingAction_hasFiniteLevel K n a f h.1,
      hk a ⟨f, hf⟩,
      isCenterFinite_finiteSmoothEnvelopingAction K n a h.2.2.1,
      hg a ⟨f, hf⟩⟩

-- Full-telescope checks retain the arbitrary field universe and all ranks.
example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @AutomorphicDifferentialInfiniteFiniteStatement

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @AutomorphicDifferentialGrowthStatement

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @AutomorphicDifferentialPreservationStatement

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @AutomorphicCompactTranslationStatement

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @AutomorphicPreservationStatement

end Langlands.Automorphic
