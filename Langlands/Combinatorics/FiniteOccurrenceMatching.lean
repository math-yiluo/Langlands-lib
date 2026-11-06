import Mathlib.Data.List.FinRange
import Mathlib.Data.Multiset.Basic
import Batteries.Data.List.Perm

/-! # Matching finite occurrences from multiset equality -/

namespace Langlands.Combinatorics

theorem exists_equiv_of_ofFn_multiset_eq {α : Type*} {r s : ℕ} (f : Fin r → α) (g : Fin s → α)
    (h : (List.ofFn f : Multiset α) = List.ofFn g) :
    ∃ e : Fin r ≃ Fin s, ∀ i, f i = g (e i) := by
  classical
  have hp : (List.ofFn f).Perm (List.ofFn g) := Quotient.exact h
  let e₀ : Fin (List.ofFn f).length ≃ Fin (List.ofFn g).length :=
    { toFun := hp.idxBij
      invFun := hp.symm.idxBij
      left_inv := hp.idxBij_symm_leftInverse_idxBij
      right_inv := hp.idxBij_symm_rightInverse_idxBij }
  let e := (finCongr (List.length_ofFn).symm).trans
    (e₀.trans (finCongr List.length_ofFn))
  refine ⟨e, fun i => ?_⟩
  have hi := hp.getElem_idxBij_eq_getElem ((finCongr (List.length_ofFn).symm) i)
  simp only [List.getElem_ofFn] at hi
  exact (congrArg f (Fin.ext rfl)).trans
    (hi.symm.trans (congrArg g (Fin.ext rfl)))

end Langlands.Combinatorics
