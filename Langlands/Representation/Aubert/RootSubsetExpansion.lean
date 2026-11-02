import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Geometric.BlockShapeCutCounts

/-! Reindex the existing actual GL Aubert sum by the coordinates of Levi roots. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

/-- A standard Levi's simple-root indices are the adjacent positions inside its blocks. -/
def leviRootSubsetEquiv (n : ℕ) : BlockShape n ≃ Finset (Fin (n - 1)) where
  toFun B := B.cutsᶜ
  invFun I := (cutEquiv n).symm Iᶜ
  left_inv B := by
    apply cuts_injective
    simp
  right_inv I := by simp

@[simp] theorem leviRootSubsetEquiv_apply {n : ℕ} (B : BlockShape n) :
    leviRootSubsetEquiv n B = B.uncuts := rfl

@[simp] theorem leviRootSubsetEquiv_card {n : ℕ} (B : BlockShape n) :
    (leviRootSubsetEquiv n B).card = n - B.length :=
  B.uncuts_card

@[simp] theorem leviRootSubsetEquiv_rankZero (B : BlockShape 0) :
    leviRootSubsetEquiv 0 B = ∅ := by
  exact Finset.eq_empty_of_isEmpty (α := Fin 0) _

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Aubert

universe uF uV

open Parabolic GeneralLinear.BlockShape

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The already constructed actual GL operator as a sum indexed by Levi-root subsets.
The empty-root-set convention includes rank zero. -/
theorem alternatingOperator_eq_rootSubset_sum (n : ℕ) :
    letI := T.topology
    alternatingOperator.{uF, uV} F T n =
      ∑ I : Finset (Fin (n - 1)), ((-1 : ℤ) ^ I.card) •
        (normalizedInductionK0.{uF, uV} F T ((leviRootSubsetEquiv n).symm I)).comp
          (normalizedJacquetK0.{uF, uV} F T ((leviRootSubsetEquiv n).symm I)) := by
  let := T.topology
  let : Fintype (GeneralLinear.BlockShape n) := Fintype.ofFinite _
  rw [alternatingOperator_eq_sum]
  refine Fintype.sum_equiv (leviRootSubsetEquiv n) _ _ ?_
  intro B
  have hB : (leviRootSubsetEquiv n).symm (leviRootSubsetEquiv n B) = B :=
    (leviRootSubsetEquiv n).symm_apply_apply B
  rw [hB, leviRootSubsetEquiv_card]

end Langlands.Aubert
