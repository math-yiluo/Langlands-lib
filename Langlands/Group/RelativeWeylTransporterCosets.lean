import Langlands.Group.RelativeWeylMinimalUniqueProof
import Langlands.Group.RelativeWeylConjugation
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Minimal transporters and source Weyl cosets

Distinct minimal double-coset representatives which transport an injectively
indexed family cannot have the same source-subgroup coset.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v z

variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {X : Type z} [MulAction W X]

/-- Minimal transporters from a fixed source, retaining their target index and
an additional selection predicate. -/
def minimalTransporterPairs (x : Finset B → X) (I : Finset B)
    (P : Finset B → W → Prop) : Set (Finset B × W) :=
  {p | IsMinimal cs p.1 I p.2 ∧ p.2 • x I = x p.1 ∧ P p.1 p.2}

/-- Source-subgroup cosets containing a selected transporter to some member
of the indexed family. -/
def transporterSourceCosets (x : Finset B → X) (I : Finset B)
    (P : Finset B → W → Prop) : Set (W ⧸ standardSubgroup cs I) :=
  (QuotientGroup.mk : W → W ⧸ standardSubgroup cs I) ''
    {w | ∃ J, w • x I = x J ∧ P J w}

/-- Equal source cosets act identically on a point fixed by the source
subgroup. -/
theorem smul_eq_of_sourceCoset_eq (x : X) (I : Finset B)
    (hfix : ∀ a ∈ standardSubgroup cs I, a • x = x)
    {w v : W}
    (h : (QuotientGroup.mk w : W ⧸ standardSubgroup cs I) =
      QuotientGroup.mk v) :
    w • x = v • x := by
  have hv : w⁻¹ * v ∈ standardSubgroup cs I := QuotientGroup.eq.mp h
  calc
    w • x = w • ((w⁻¹ * v) • x) := by rw [hfix _ hv]
    _ = v • x := by rw [← mul_smul]; simp

/-- Minimal transporters with the same source coset have the same target
index and Weyl element. -/
theorem minimalTransporterCoset_injective (x : Finset B → X)
    (hx : Function.Injective x) (I : Finset B)
    (hfix : ∀ a ∈ standardSubgroup cs I, a • x I = x I)
    (P : Finset B → W → Prop) :
    Function.Injective
      (fun p : minimalTransporterPairs cs x I P =>
        (QuotientGroup.mk p.val.2 : W ⧸ standardSubgroup cs I)) := by
  intro p q hpq
  have hJ : p.val.1 = q.val.1 := hx <| by
    rw [← p.property.2.1, ← q.property.2.1]
    exact smul_eq_of_sourceCoset_eq cs (x I) I hfix hpq
  have hw : p.val.2 = q.val.2 := by
    apply minimalRepresentativeUnique_proof cs p.val.1 I p.val.2 p.val.2 q.val.2
      (mem_doubleCoset_self cs _ _ _)
    · exact ⟨1, (standardSubgroup cs p.val.1).one_mem,
        p.val.2⁻¹ * q.val.2, QuotientGroup.eq.mp hpq, by simp⟩
    · exact p.property.1
    · rw [hJ]
      exact q.property.1
  exact Subtype.ext (Prod.ext hJ hw)

/-- The injection used to compare geometric-filtration multiplicities with
the source Weyl-coset count. -/
def minimalTransporterCosetEmbedding (x : Finset B → X)
    (hx : Function.Injective x) (I : Finset B)
    (hfix : ∀ a ∈ standardSubgroup cs I, a • x I = x I)
    (P : Finset B → W → Prop) :
    minimalTransporterPairs cs x I P ↪ transporterSourceCosets cs x I P where
  toFun p := ⟨QuotientGroup.mk p.val.2,
    ⟨p.val.2, ⟨p.val.1, p.property.2⟩, rfl⟩⟩
  inj' p q h := minimalTransporterCoset_injective cs x hx I hfix P
    (congrArg Subtype.val h)

/-- Finiteness of the Weyl group suffices for the transporter count bound;
the family itself need not be finite. -/
theorem card_minimalTransporterPairs_le [Finite W] (x : Finset B → X)
    (hx : Function.Injective x) (I : Finset B)
    (hfix : ∀ a ∈ standardSubgroup cs I, a • x I = x I)
    (P : Finset B → W → Prop) :
    Nat.card (minimalTransporterPairs cs x I P) ≤
      Nat.card (transporterSourceCosets cs x I P) :=
  Nat.card_le_card_of_injective
    (minimalTransporterCosetEmbedding cs x hx I hfix P)
    (minimalTransporterCosetEmbedding cs x hx I hfix P).injective

end Langlands.Group.RelativeWeylIndexing
