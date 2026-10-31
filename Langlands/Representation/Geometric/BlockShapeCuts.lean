import Langlands.Representation.CuspidalSupport.FiniteBlockShapes

/-! Ordered positive block shapes as their sets of interior cuts. -/

namespace Langlands.GeneralLinear.BlockShape

variable {n : ℕ}

/-- Recover an ordered block shape from a composition of its total rank. -/
def ofComposition (c : Composition n) : BlockShape n where
  length := c.length
  size := c.blocksFun
  positive := c.one_le_blocksFun
  sum_eq := c.sum_blocksFun

@[simp] theorem toComposition_ofComposition (c : Composition n) :
    (ofComposition c).toComposition = c := by
  apply Composition.ext
  exact c.ofFn_blocksFun

@[simp] theorem ofComposition_toComposition (B : BlockShape n) :
    ofComposition B.toComposition = B := by
  apply toComposition_injective
  exact toComposition_ofComposition B.toComposition

/-- The list and indexed-function descriptions of an ordered block shape agree. -/
def compositionEquiv (n : ℕ) : BlockShape n ≃ Composition n where
  toFun := toComposition
  invFun := ofComposition
  left_inv := ofComposition_toComposition
  right_inv := toComposition_ofComposition

@[simp] theorem compositionEquiv_apply (B : BlockShape n) :
    compositionEquiv n B = B.toComposition := rfl

@[simp] theorem compositionEquiv_symm_apply (c : Composition n) :
    (compositionEquiv n).symm c = ofComposition c := rfl

/-- A cut at `i` is the boundary after coordinate `i`, hence at position `i + 1`. -/
def cutEquiv (n : ℕ) : BlockShape n ≃ Finset (Fin (n - 1)) :=
  (compositionEquiv n).trans
    ((_root_.compositionEquiv n).trans (compositionAsSetEquiv n))

/-- The interior boundaries of an ordered block shape, shifted left by one. -/
def cuts (B : BlockShape n) : Finset (Fin (n - 1)) :=
  cutEquiv n B

@[simp] theorem cutEquiv_apply (B : BlockShape n) :
    cutEquiv n B = B.cuts := rfl

@[simp] theorem cuts_cutEquiv_symm (s : Finset (Fin (n - 1))) :
    ((cutEquiv n).symm s).cuts = s :=
  (cutEquiv n).apply_symm_apply s

@[simp] theorem cutEquiv_symm_cuts (B : BlockShape n) :
    (cutEquiv n).symm B.cuts = B :=
  (cutEquiv n).symm_apply_apply B

theorem cuts_injective : Function.Injective (cuts (n := n)) :=
  (cutEquiv n).injective

@[simp] theorem cuts_inj {B C : BlockShape n} :
    B.cuts = C.cuts ↔ B = C :=
  cuts_injective.eq_iff

/-- Membership means that the corresponding positive interior position is a boundary. -/
theorem mem_cuts_iff (B : BlockShape n) (i : Fin (n - 1)) :
    i ∈ B.cuts ↔
      (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ∈ B.toComposition.boundaries := by
  change i ∈ {j : Fin (n - 1) |
    (⟨1 + j.val, by omega⟩ : Fin (n + 1)) ∈ B.toComposition.boundaries}.toFinset ↔ _
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Nat.add_comm]

end Langlands.GeneralLinear.BlockShape
