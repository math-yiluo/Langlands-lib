import Langlands.Representation.Aubert.InductionCommutationAssembly
import Langlands.Representation.Aubert.RankZero
import Langlands.Representation.Geometric.GrothendieckProof
import Langlands.Representation.Geometric.InducedPieceGrothendieck

/-! Actual Aubert commutation with normalized induction in every rank. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual normalized induction intertwines the unadjusted Aubert operators
on the full exact finite-length Grothendieck groups in every natural rank. -/
theorem inductionCommutation :
    InductionCommutationStatement.{uF, uV} F T := by
  let := T.topology
  intro n B
  cases n with
  | zero => exact inductionCommutation_rankZero.{uF, uV} F T B
  | succ n =>
      apply inductionCommutation_positive_of_piece_comparison.{uF, uV} F T
        (geometricLemmaGrothendieck.{uF, uV} F T) (Nat.succ_pos n) B
      intro C w S R hS hR x
      exact LinearMap.congr_fun
        (normalizedInductionK0_comp_geometricPieceK0.{uF, uV}
          F T B C w.val S R hS hR) x

end Langlands.Aubert
