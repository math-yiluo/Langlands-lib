import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-! # A finite family as a multiset sum -/

namespace Langlands.Classification.SegmentProductCuspidalEmbedding

theorem ofFn_multiset_eq_sum {α : Type*} {k : ℕ} (f : Fin k → α) :
    (List.ofFn f : Multiset α) = ∑ i, ({f i} : Multiset α) := by
  simpa only [Multiset.map_coe, List.map_ofFn, Multiset.sum_coe, List.sum_ofFn,
    Function.comp_apply] using (Multiset.sum_map_singleton (List.ofFn f : Multiset α)).symm

end Langlands.Classification.SegmentProductCuspidalEmbedding
