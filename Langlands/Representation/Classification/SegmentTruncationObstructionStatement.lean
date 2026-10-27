import Langlands.Representation.Classification.Segments

/-!
# The finite segment-truncation obstruction

The combinatorial lemma of Zelevinsky 1980, §9.8, printed pp.199–200.
An optional actual segment represents a possibly empty truncation.
This module states the obstruction and does not prove it.
-/

namespace Langlands

universe uF uV

namespace PadicField.TopologicalData.Segment

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The empty support for `none`, and the actual segment support for `some E`. -/
def optionalSupport (A : Option (T.Segment.{uV, uF})) :
    Set (T.CuspidalDatum.{uV, uF}) :=
  match A with
  | none => ∅
  | some E => E.support

/-- A possibly empty terminal subsegment of `Δ`, retaining its last member. -/
def IsTerminalTruncation (A : Option (T.Segment.{uV, uF}))
    (Δ : T.Segment.{uV, uF}) : Prop :=
  match A with
  | none => True
  | some E => E.support ⊆ Δ.support ∧ Δ.last ∈ E.support

/-- A possibly empty initial subsegment of `Δ`, retaining its base. -/
def IsInitialTruncation (B : Option (T.Segment.{uV, uF}))
    (Δ : T.Segment.{uV, uF}) : Prop :=
  match B with
  | none => True
  | some E => E.support ⊆ Δ.support ∧ Δ.base ∈ E.support

end PadicField.TopologicalData.Segment

namespace Classification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Nonempty equality of the initial-truncation union with the one-step twist of
the terminal-truncation union forces a linked pair in the original finite family.
Repeated segments and the empty index family are allowed. -/
def SegmentTruncationObstruction : Prop :=
  ∀ (r : ℕ) (Δ : Fin r → T.Segment.{uV, uF})
    (A B : Fin r → Option (T.Segment.{uV, uF})),
    (∀ i, PadicField.TopologicalData.Segment.IsTerminalTruncation (A i) (Δ i)) →
    (∀ i, PadicField.TopologicalData.Segment.IsInitialTruncation (B i) (Δ i)) →
    (⋃ i, PadicField.TopologicalData.Segment.optionalSupport (B i)) =
      (fun ρ : T.CuspidalDatum.{uV, uF} => ρ.twist 1) ''
        (⋃ i, PadicField.TopologicalData.Segment.optionalSupport (A i)) →
    (⋃ i, PadicField.TopologicalData.Segment.optionalSupport (B i)).Nonempty →
    ∃ i j : Fin r, (Δ i).IsLinked (Δ j)

end Classification

end Langlands
