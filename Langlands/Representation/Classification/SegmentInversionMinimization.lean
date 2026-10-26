import Langlands.Representation.Classification.SegmentBaseShift
import Langlands.Representation.Classification.SegmentReplacementInversions
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Combinatorics.RelationInversionExposure

/-! # Minimizing segment inversions under explicit local reductions

The predicate on lists and both local preservation rules are hypotheses.
This module does not prove those rules for representation embeddings.
-/

noncomputable section

open scoped Classical

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

open Langlands.Combinatorics

/-- The two local rules used by the inversion argument: unlinked adjacent
commutation and, for a preceding pair, either commutation or actual
union/intersection replacement. Every outside occurrence keeps its position. -/
def HasLocalSegmentReductions (P : List (Segment.{uV, uF} T) → Prop) : Prop :=
  (∀ (s t : List (Segment.{uV, uF} T)) (Δ Γ : Segment.{uV, uF} T),
    ¬ Δ.IsLinked Γ → P (s ++ Δ :: Γ :: t) → P (s ++ Γ :: Δ :: t)) ∧
  (∀ (s t : List (Segment.{uV, uF} T)) (Δ Γ : Segment.{uV, uF} T),
    Δ.Precedes Γ → P (s ++ Δ :: Γ :: t) →
      P (s ++ Γ :: Δ :: t) ∨
        ∃ (U : Segment.{uV, uF} T) (I : Option (Segment.{uV, uF} T)),
          Segment.IsUnionIntersectionReplacement Δ Γ U I ∧
            P (s ++ (U :: I.toList) ++ t))

/-- A list satisfying `P` whose positional precedence count is least among
all lists satisfying `P`. No finiteness condition on that collection is imposed. -/
def IsSegmentInversionMinimal (P : List (Segment.{uV, uF} T) → Prop)
    (l : List (Segment.{uV, uF} T)) : Prop :=
  P l ∧ ∀ m, P m →
    relationInversions Segment.Precedes l ≤ relationInversions Segment.Precedes m

theorem exists_segmentInversionMinimal
    {P : List (Segment.{uV, uF} T) → Prop} (hP : ∃ l, P l) :
    ∃ l, IsSegmentInversionMinimal P l := by
  classical
  have hex : ∃ k : ℕ, ∃ l, P l ∧ relationInversions Segment.Precedes l = k := by
    obtain ⟨l, hl⟩ := hP
    exact ⟨_, l, hl, rfl⟩
  obtain ⟨l, hl, hcount⟩ := Nat.find_spec hex
  refine ⟨l, hl, ?_⟩
  intro m hm
  rw [hcount]
  exact Nat.find_min' hex ⟨m, hm, rfl⟩

theorem HasLocalSegmentReductions.unrelatedSwap_preserves
    {P : List (Segment.{uV, uF} T) → Prop} (hP : HasLocalSegmentReductions P)
    (s t : List (Segment.{uV, uF} T)) (Δ Γ : Segment.{uV, uF} T)
    (hΔΓ : ¬ Δ.Precedes Γ) (hΓΔ : ¬ Γ.Precedes Δ)
    (hl : P (s ++ Δ :: Γ :: t)) : P (s ++ Γ :: Δ :: t) := by
  apply hP.1 s t Δ Γ _ hl
  intro hlinked
  exact hlinked.precedes_or_precedes.elim hΔΓ hΓΔ

/-- Every inversion-minimal list is nonprecedence ordered, provided the two
local rules and integral twist freeness are supplied. -/
theorem IsSegmentInversionMinimal.isPrecedenceOrderedList
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {P : List (Segment.{uV, uF} T) → Prop} (hP : HasLocalSegmentReductions P)
    {l : List (Segment.{uV, uF} T)} (hl : IsSegmentInversionMinimal P l) :
    T.IsPrecedenceOrderedList l := by
  classical
  apply (relationInversions_eq_zero_iff Segment.Precedes l).mp
  by_contra hzero
  have hpos : 0 < relationInversions Segment.Precedes l := Nat.pos_of_ne_zero hzero
  obtain ⟨s, t, Δ, Γ, hreach, hp⟩ :=
    exists_adjacent_relation_of_inversions_pos
      (Segment.not_transGen_precedes_self hfree) hpos
  have hexposed : P (s ++ Δ :: Γ :: t) :=
    hreach.preserves hP.unrelatedSwap_preserves hl.1
  have hcount := hreach.inversions_eq
  rcases hP.2 s t Δ Γ hp hexposed with hswap | ⟨U, I, hs, hreplace⟩
  · have hlt := relationInversions_swap_related_lt Segment.Precedes s t Δ Γ hp
      (hp.not_reverse hfree)
    have hle := hl.2 _ hswap
    omega
  · have hlt := hs.inversions_replace_lt hfree hp s t
    have hle := hl.2 _ hreplace
    have hcount' : relationInversions Segment.Precedes (s ++ [Δ, Γ] ++ t) =
        relationInversions Segment.Precedes l := by simpa using hcount
    omega

/-- A nonempty collection closed under the specified local reductions contains
a genuine list with no earlier segment preceding a later segment. -/
theorem HasLocalSegmentReductions.exists_ordered
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {P : List (Segment.{uV, uF} T) → Prop} (hP : HasLocalSegmentReductions P)
    (hne : ∃ l, P l) :
    ∃ l, P l ∧ T.IsPrecedenceOrderedList l := by
  obtain ⟨l, hl⟩ := exists_segmentInversionMinimal hne
  exact ⟨l, hl.1, hl.isPrecedenceOrderedList hfree hP⟩

end Langlands.PadicField.TopologicalData
