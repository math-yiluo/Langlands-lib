import Langlands.Representation.Classification.LeftCuspidalDerivativeStatement
import Langlands.Representation.Classification.SegmentHeadSupportGeneric

/-!
# Basic facts on left reducedness
-/

noncomputable section

namespace Langlands.Classification.LeftCuspidalDerivative

open CategoryTheory PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Clause 1: left reducedness passes to subquotients. -/
theorem leftReduced_of_isSubquotient {d : ℕ}
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {m : ℕ} {Y Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (h : letI := T.topology; SmoothRep.IsSubquotient Y' Y) (hY : LeftReduced F T A Y) :
    LeftReduced F T A Y' := by
  let := T.topology
  intro Z hZ hZY k hk σ
  exact hY Z hZ (SegmentHeadSupport.isSubquotient_trans hZY h) k hk σ

end Langlands.Classification.LeftCuspidalDerivative
