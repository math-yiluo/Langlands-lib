import Langlands.Group.RelativeWeylTransporterCosets

/-!
# Source-coset bounds for actual relative Weyl transporters

The selected condition can depend on the normalizer lift and its actual
Levi-conjugation equality, as representation transport does.
-/

namespace Langlands.Group.RelativeWeylIndexing

open RelativeWeyl

universe u v

variable {B : Type u} {G : Type v} [Group G]
variable (T : Subgroup G) (L : Finset B → Subgroup G)
variable {M : CoxeterMatrix B} (actual : ActualCoxeterSystem T M)

/-- Regard an actual family containing the full centralizer as a family in
the Weyl conjugation action. -/
def actualOvergroupFamily (hZ : ∀ J, centralizer T ≤ L J) :
    Finset B → CentralizerOvergroup T :=
  fun J => ⟨L J, hZ J⟩

theorem actualOvergroupFamily_injective (hZ : ∀ J, centralizer T ≤ L J)
    (hL : Function.Injective L) :
    Function.Injective (actualOvergroupFamily T L hZ) := by
  intro I J h
  exact hL (congrArg Subtype.val h)

/-- The generated source Weyl subgroup fixes its actual Levi, when its
identification with the Levi Weyl image is known. -/
theorem standardSubgroup_smul_actualOvergroup
    (hZ : ∀ J, centralizer T ≤ L J)
    (hIdent : actualLeviWeylIdentification T L actual)
    (I : Finset B) (w : Weyl T) (hw : w ∈ standardSubgroup actual I) :
    w • actualOvergroupFamily T L hZ I = actualOvergroupFamily T L hZ I := by
  rw [← hIdent I] at hw
  obtain ⟨v, rfl⟩ := hw
  exact inclusion_smul_overgroup T (L I) (hZ I) v

variable (I : Finset B)
variable (Q : ∀ (J : Finset B) (n : normalizer T),
  (L I).map (MulAut.conj (n : G) : G →* G) = L J → Prop)

/-- A selected actual transporter, with its lift and literal subgroup
conjugation equality retained. -/
def actualTransporterSelection (J : Finset B) (w : Weyl T) : Prop :=
  ∃ (n : normalizer T)
    (h : (L I).map (MulAut.conj (n : G) : G →* G) = L J),
    (QuotientGroup.mk n : Weyl T) = w ∧ Q J n h

/-- Minimal selected transporters between actual members of the family. -/
def actualMinimalTransporterPairs : Set (Finset B × Weyl T) :=
  {p | IsMinimal actual p.1 I p.2 ∧
    actualTransporterSelection T L I Q p.1 p.2}

/-- Selected source cosets in the actual quotient by the image of the
source Levi Weyl group. -/
def actualTransporterSourceCosets :
    Set (Weyl T ⧸ (inclusion T (L I)).range) :=
  (QuotientGroup.mk : Weyl T → Weyl T ⧸ (inclusion T (L I)).range) ''
    {w | ∃ J, actualTransporterSelection T L I Q J w}

theorem actualTransporterSelection_smul (hZ : ∀ J, centralizer T ≤ L J)
    {J : Finset B} {w : Weyl T}
    (hw : actualTransporterSelection T L I Q J w) :
    w • actualOvergroupFamily T L hZ I =
      actualOvergroupFamily T L hZ J := by
  obtain ⟨n, h, rfl, _⟩ := hw
  apply Subtype.ext
  exact h

/-- Minimal actual transporters inject into the exact source-coset image,
including conditions on representation transport along their lifts. -/
def actualMinimalTransporterCosetEmbedding
    (hZ : ∀ J, centralizer T ≤ L J)
    (hL : Function.Injective L)
    (hIdent : actualLeviWeylIdentification T L actual) :
    actualMinimalTransporterPairs T L actual I Q ↪
      actualTransporterSourceCosets T L I Q where
  toFun p := ⟨QuotientGroup.mk p.val.2,
    ⟨p.val.2, ⟨p.val.1, p.property.2⟩, rfl⟩⟩
  inj' p q h := by
    let x := actualOvergroupFamily T L hZ
    let P := actualTransporterSelection T L I Q
    let f : actualMinimalTransporterPairs T L actual I Q →
        minimalTransporterPairs actual x I P := fun r =>
      ⟨r.val, r.property.1,
        actualTransporterSelection_smul T L I Q hZ r.property.2,
        r.property.2⟩
    have heq : (QuotientGroup.mk p.val.2 :
        Weyl T ⧸ standardSubgroup actual I) = QuotientGroup.mk q.val.2 := by
      apply QuotientGroup.eq.mpr
      rw [← hIdent I]
      exact QuotientGroup.eq.mp (congrArg Subtype.val h)
    have hf : f p = f q :=
      minimalTransporterCoset_injective actual x
        (actualOvergroupFamily_injective T L hZ hL) I
        (standardSubgroup_smul_actualOvergroup T L actual hZ hIdent I) P heq
    exact Subtype.ext
      (congrArg (fun r : minimalTransporterPairs actual x I P => r.val) hf)

/-- The corresponding bound in the finite actual relative Weyl group. -/
theorem card_actualMinimalTransporterPairs_le [Finite (Weyl T)]
    (hZ : ∀ J, centralizer T ≤ L J)
    (hL : Function.Injective L)
    (hIdent : actualLeviWeylIdentification T L actual) :
    Nat.card (actualMinimalTransporterPairs T L actual I Q) ≤
      Nat.card (actualTransporterSourceCosets T L I Q) :=
  Nat.card_le_card_of_injective
    (actualMinimalTransporterCosetEmbedding T L actual I Q hZ hL hIdent)
    (actualMinimalTransporterCosetEmbedding T L actual I Q hZ hL hIdent).injective

end Langlands.Group.RelativeWeylIndexing
