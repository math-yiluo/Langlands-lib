import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Langlands.Cohomology.Tate.ZeroDefinitions

/-! # Statements of the cyclic Herbrand calculus for ordinary group cohomology -/

namespace Langlands.GroupTheory

universe u

open CategoryTheory

/-- Division-free Herbrand multiplicativity, including finiteness in each of the
three two-out-of-three cases of a short exact sequence. -/
def CyclicHerbrandShortExact : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G] [Finite G] [IsCyclic G]
    (S : ShortComplex (Rep.{u} k G)), S.ShortExact →
    (Finite (groupCohomology S.X₁ 1) → Finite (groupCohomology S.X₁ 2) →
      Finite (groupCohomology S.X₃ 1) → Finite (groupCohomology S.X₃ 2) →
      Finite (groupCohomology S.X₂ 1) ∧ Finite (groupCohomology S.X₂ 2) ∧
        Nat.card (groupCohomology S.X₂ 2) * Nat.card (groupCohomology S.X₁ 1) *
            Nat.card (groupCohomology S.X₃ 1) =
          Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
            Nat.card (groupCohomology S.X₃ 2)) ∧
    (Finite (groupCohomology S.X₂ 1) → Finite (groupCohomology S.X₂ 2) →
      Finite (groupCohomology S.X₃ 1) → Finite (groupCohomology S.X₃ 2) →
      Finite (groupCohomology S.X₁ 1) ∧ Finite (groupCohomology S.X₁ 2) ∧
        Nat.card (groupCohomology S.X₂ 2) * Nat.card (groupCohomology S.X₁ 1) *
            Nat.card (groupCohomology S.X₃ 1) =
          Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
            Nat.card (groupCohomology S.X₃ 2)) ∧
    (Finite (groupCohomology S.X₁ 1) → Finite (groupCohomology S.X₁ 2) →
      Finite (groupCohomology S.X₂ 1) → Finite (groupCohomology S.X₂ 2) →
      Finite (groupCohomology S.X₃ 1) ∧ Finite (groupCohomology S.X₃ 2) ∧
        Nat.card (groupCohomology S.X₂ 2) * Nat.card (groupCohomology S.X₁ 1) *
            Nat.card (groupCohomology S.X₃ 1) =
          Nat.card (groupCohomology S.X₂ 1) * Nat.card (groupCohomology S.X₁ 2) *
            Nat.card (groupCohomology S.X₃ 2))

/-- A finite coefficient representation has finite first and second ordinary
cohomology of equal cardinality. -/
def CyclicHerbrandFiniteCoefficients : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G] [Finite G] [IsCyclic G]
    (V : Rep.{u} k G) [Finite V],
    Finite (groupCohomology V 1) ∧ Finite (groupCohomology V 2) ∧
      Nat.card (groupCohomology V 2) = Nat.card (groupCohomology V 1)

/-- For the published trivial representation on lifted integers, the first
ordinary cohomology group is trivial and the second is finite of order `|G|`. -/
def CyclicHerbrandTrivialIntegers : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsCyclic G],
    Subsingleton (groupCohomology (Langlands.Tate.integralTrivial G) 1) ∧
      Finite (groupCohomology (Langlands.Tate.integralTrivial G) 2) ∧
      Nat.card (groupCohomology (Langlands.Tate.integralTrivial G) 2) = Nat.card G

/-- The three cyclic Herbrand calculus statements, bundled as a single exact
proof target. This definition asserts no proof of its constituent statements. -/
def CyclicHerbrandCalculus : Prop :=
  CyclicHerbrandShortExact.{u} ∧ CyclicHerbrandFiniteCoefficients.{u} ∧
    CyclicHerbrandTrivialIntegers.{u}

end Langlands.GroupTheory
