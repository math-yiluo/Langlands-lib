import Langlands.Representation.Classification.HighestDerivativeSupportShiftBoundary
import Mathlib.Data.Nat.Find

/-! # Choosing an actual highest positive general-linear derivative order -/

noncomputable section

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A feasible positive order with nonzero actual derivative and vanishing of
every higher feasible derivative. -/
structure GeneralLinearHighestDerivativeOrderData {N : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) where
  order : ℕ
  le_rank : order ≤ N
  positive : 0 < order
  nonzero : letI := T.topology
    Nontrivial ((generalLinearDerivative T ψ N order le_rank).obj A)
  higher_vanish : letI := T.topology
    ∀ (j : ℕ) (hj : j ≤ N), order < j →
      Subsingleton ((generalLinearDerivative T ψ N j hj).obj A)

/-- Select a highest positive derivative order of any nonzero smooth
general-linear representation of positive rank. -/
def chooseGeneralLinearHighestDerivativeOrder {N : ℕ} (hN : 0 < N)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier))
    (hA : Nontrivial A) : GeneralLinearHighestDerivativeOrderData T ψ A := by
  letI := T.topology
  classical
  let P : ℕ → Prop := fun j =>
    ∃ hj : j ≤ N, Nontrivial ((generalLinearDerivative T ψ N j hj).obj A)
  let k := Nat.findGreatest P N
  have hk : k ≤ N := Nat.findGreatest_le N
  have hzero : P 0 := ⟨Nat.zero_le N, hA⟩
  have hspec : P k := Nat.findGreatest_spec (Nat.zero_le N) hzero
  have hnonzero : Nontrivial ((generalLinearDerivative T ψ N k hk).obj A) :=
    hspec.choose_spec
  have hhigh : ∀ (j : ℕ) (hj : j ≤ N), k < j →
      Subsingleton ((generalLinearDerivative T ψ N j hj).obj A) := by
    intro j hj hkj
    rw [← not_nontrivial_iff_subsingleton]
    intro hjnonzero
    exact Nat.findGreatest_is_greatest hkj hj ⟨hj, hjnonzero⟩
  exact {
    order := k
    le_rank := hk
    positive := highestGeneralLinearDerivativeOrder_pos T ψ hN hk A hnonzero hhigh
    nonzero := hnonzero
    higher_vanish := hhigh }

end Langlands.Derivative
