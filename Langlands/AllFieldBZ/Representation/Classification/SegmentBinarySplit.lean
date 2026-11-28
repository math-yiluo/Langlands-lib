import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.Group.GL.MirabolicOppositeIntersection
import Langlands.Group.GL.SingleBlock

/-! Initial and terminal pieces of a two-block segment split. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.Segment

open Langlands.GeneralLinear

universe uF uV

variable {F : LocalFieldPackage.{uF}} {T : F.TopologicalData}

/-- The first `q` members of the segment's increasing order. -/
def initial (Δ : Segment.{uV,uF} T) (q : ℕ) (hq : 0 < q) : Segment.{uV,uF} T :=
  ⟨Δ.base, q, hq⟩

/-- The remaining members of the increasing order after the first `q`. -/
def terminal (Δ : Segment.{uV,uF} T) (q : ℕ) (hq : q < Δ.length) : Segment.{uV,uF} T :=
  ⟨Δ.member q, Δ.length - q, Nat.sub_pos_of_lt hq⟩

theorem initial_degree_add_terminal_degree (Δ : Segment.{uV,uF} T)
    (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length) :
    (Δ.initial q hq).degree + (Δ.terminal q hqm).degree = Δ.degree := by
  change q * Δ.rank + (Δ.length - q) * Δ.rank = Δ.length * Δ.rank
  rw [← Nat.add_mul, Nat.add_sub_of_le hqm.le]

/-- The two-block shape carrying that split in the increasing order. -/
def splitShape (Δ : Segment.{uV,uF} T) (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length) :
    BlockShape Δ.degree :=
  (BlockShape.binary (Δ.initial q hq).degree (Δ.terminal q hqm).degree
    (Δ.initial q hq).degree_pos (Δ.terminal q hqm).degree_pos).rankCast
      (Δ.initial_degree_add_terminal_degree q hq hqm)

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.Segment
