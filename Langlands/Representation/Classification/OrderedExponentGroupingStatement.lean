import Langlands.Group.GL.Blocks
import Mathlib.Basic.Real.Basic

/-! Finite ordered equal-exponent runs with weighted block coordinates. -/

namespace Langlands.Classification

open GeneralLinear

/-- An antitone exponent list on positive ordered blocks admits consecutive
constant runs, with every weighted inner coordinate retained exactly. -/
def OrderedExponentGrouping : Prop :=
  ∀ (n : ℕ) (B : BlockShape n) (a : Fin B.length → ℝ), Antitone a →
    ∃ (D : BlockShape n) (b : Fin D.length → ℝ)
      (q : Fin B.length → Fin D.length),
      StrictAnti b ∧ Monotone q ∧ Function.Surjective q ∧
      (∀ i, a i = b (q i)) ∧
      ∃ (S : ∀ j, BlockShape (D.size j))
        (e : ∀ j, Fin (S j).length ≃ {i : Fin B.length // q i = j})
        (h : ∀ j k, (S j).size k = B.size (e j k).val),
        (∀ j, StrictMono (fun k => (e j k).val)) ∧
        (∀ j k (x : Fin ((S j).size k)),
          D.index j ((S j).index k x) =
            B.index (e j k).val (Fin.cast (h j k) x))

end Langlands.Classification
