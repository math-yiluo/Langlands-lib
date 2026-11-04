import Langlands.CategoryTheory.Renard.FilteredColimit

/-!
# Renard A.IV.2: directed quotient universal properties and eventual zero

Proposition-valued targets over the actual published quotient and cocones.
Index, component and target universes are independent. The empty diagram
uses its singleton cocone, while the literal quotient group requires nonemptiness.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.FilteredColimit

universe uI uG uH

/-- The concrete quotient cocone is colimiting for a nonempty directed index. -/
def QuotientColimitStatement : Prop :=
  ∀ (I : Type uI) [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (G : I → Type uG) [∀ i, AddCommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G (f · · ·)],
    Nonempty (IsColimit (cocone G f))

/-- The actual quotient lift factors each compatible family and is the unique
additive homomorphism doing so, for a target in an independent universe. -/
def CompatibleFamilyLiftStatement : Prop :=
  ∀ (I : Type uI) [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (G : I → Type uG) [∀ i, AddCommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G (f · · ·)]
    (H : Type uH) [AddCommGroup H]
    (g : ∀ i, G i →+ H)
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x),
    (∀ i, (lift G f g hg).comp (of G f i) = g i) ∧
      ∀ l : Carrier G f →+ H,
        (∀ i, l.comp (of G f i) = g i) → l = lift G f g hg

/-- Source A.IV.2: a representative whose class vanishes becomes zero at
some later stage. -/
def EventualZeroStatement : Prop :=
  ∀ (I : Type uI) [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (G : I → Type uG) [∀ i, AddCommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G (f · · ·)]
    (i : I) (x : G i),
    of G f i x = 0 → ∃ (j : I) (hij : i ≤ j), f i j hij x = 0

/-- Derived strengthening: vanishing of the class is equivalent to vanishing
after one transition. The reverse implication uses transition compatibility. -/
def EventualZeroIffStatement : Prop :=
  ∀ (I : Type uI) [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (G : I → Type uG) [∀ i, AddCommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G (f · · ·)]
    (i : I) (x : G i),
    of G f i x = 0 ↔ ∃ (j : I) (hij : i ≤ j), f i j hij x = 0

/-- The actual singleton cocone is a colimit for the empty ordered diagram. -/
def EmptyColimitStatement : Prop :=
  ∀ (I : Type uI) [PartialOrder I] [IsEmpty I]
    (G : I → Type uG) [∀ i, AddCommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G (f · · ·)],
    Nonempty (IsColimit (emptyCocone G f))

/-- The concrete quotient conclusions, followed by the separate empty case. -/
def FilteredColimitStatements : Prop :=
  QuotientColimitStatement.{uI, uG} ∧
    CompatibleFamilyLiftStatement.{uI, uG, uH} ∧
      EventualZeroStatement.{uI, uG} ∧
        EventualZeroIffStatement.{uI, uG} ∧
          EmptyColimitStatement.{uI, uG}

end Langlands.Renard.FilteredColimit
