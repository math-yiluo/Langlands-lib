import Langlands.Representation.Classification.MoeglinWaldspurger

/-! # Unproved combinatorial MW targets -/

namespace Langlands.MoeglinWaldspurger

/-- The output retains every integer support point with its multiplicity. Unproved. -/
def SupportPreservation : Prop := ∀ a : Multisegment, support (dual a) = support a

/-- The recursive output is an involution on all finite multisegments. Unproved. -/
def Involutivity : Prop := ∀ a : Multisegment, dual (dual a) = a

/-- Badulescu (P): `k` consecutive possible input endings bound each output length.
The half-open integer range `[b,b+k)` has exactly `k` points. Unproved. -/
def EndingBound : Prop :=
  ∀ (a : Multisegment) (b : ℤ) (k : ℕ),
    (∀ I ∈ a, b ≤ I.ending ∧ I.ending < b + (k : ℤ)) →
    ∀ J ∈ dual a, J.length ≤ k

/-- Badulescu (P'): each output length is at most the input thickness. Unproved. -/
def ThicknessBound : Prop :=
  ∀ a : Multisegment, ∀ J ∈ dual a, J.length ≤ a.card

/-- The four separately named, unproved combinatorial targets. -/
def CombinatorialProperties : Prop :=
  SupportPreservation ∧ Involutivity ∧ EndingBound ∧ ThicknessBound

end Langlands.MoeglinWaldspurger
