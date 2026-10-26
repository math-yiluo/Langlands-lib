import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Renard's sequence definitions of exact functors

The functor is additive throughout, as assumed in Renard A.VIII.1.
These predicates use the source's one-sided exact sequences.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Langlands.Renard

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

section Covariant

variable (F : C ⥤ D) [F.Additive]

/-- Preservation of every exact sequence `0 ⟶ X ⟶ Y ⟶ Z`, in Renard A.VIII.1. -/
def SequenceLeftExact : Prop :=
  ∀ S : ShortComplex C,
    S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)

/-- Preservation of every exact sequence `X ⟶ Y ⟶ Z ⟶ 0`, in Renard A.VIII.1. -/
def SequenceRightExact : Prop :=
  ∀ S : ShortComplex C,
    S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g)

/-- Renard's exactness condition is left and right sequence exactness together. -/
def SequenceExact : Prop :=
  SequenceLeftExact F ∧ SequenceRightExact F

/-- Unfold the source's left exactness condition. -/
theorem sequenceLeftExact_iff :
    SequenceLeftExact F ↔
      ∀ S : ShortComplex C,
        S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f) :=
  Iff.rfl

/-- Unfold the source's right exactness condition. -/
theorem sequenceRightExact_iff :
    SequenceRightExact F ↔
      ∀ S : ShortComplex C,
        S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g) :=
  Iff.rfl

/-- Unfold two-sided exactness as the conjunction in the source. -/
theorem sequenceExact_iff :
    SequenceExact F ↔ SequenceLeftExact F ∧ SequenceRightExact F :=
  Iff.rfl

end Covariant

section Contravariant

variable (F : Cᵒᵖ ⥤ D) [F.Additive]

/-- Renard's contravariant left exactness is covariant left exactness on `Cᵒᵖ`. -/
abbrev ContravariantSequenceLeftExact : Prop :=
  SequenceLeftExact F

/-- Renard's contravariant right exactness is covariant right exactness on `Cᵒᵖ`. -/
abbrev ContravariantSequenceRightExact : Prop :=
  SequenceRightExact F

/-- Apply Renard's two-sided sequence condition to the actual functor `Cᵒᵖ ⥤ D`. -/
abbrev ContravariantSequenceExact : Prop :=
  SequenceExact F

end Contravariant

end Langlands.Renard
