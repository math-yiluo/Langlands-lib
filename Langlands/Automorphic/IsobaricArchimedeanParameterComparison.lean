import Langlands.Automorphic.ArchimedeanPlaceParameterClasses
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Bind

/-! # Pooling the archimedean parameters of matched cuspidal classes -/

open scoped BigOperators

set_option autoImplicit false

universe u uA uB

namespace Langlands.Automorphic

open Langlands.Global

private theorem coe_flatten_ofFn {α : Type uA} {k : ℕ} (a : Fin k → List α) :
    ((List.ofFn a).flatten : Multiset α) = ∑ i, (a i : Multiset α) := by
  rw [← Multiset.coe_join, List.map_ofFn]
  change (↑(List.ofFn fun i => (a i : Multiset α)) : Multiset (Multiset α)).sum = _
  rw [Multiset.sum_coe, List.sum_ofFn]

private theorem flatMap_flatten_ofFn {α : Type uA} {β : Type uB} {k : ℕ}
    (a : Fin k → List α) (expand : α → List β) :
    (List.ofFn a).flatten.flatMap expand =
      (List.ofFn fun i => (a i).flatMap expand).flatten := by
  have h (L : List (List α)) : L.flatten.flatMap expand =
      (L.map (fun l => l.flatMap expand)).flatten := by
    induction L with
    | nil => rfl
    | cons l L ih => simp only [List.flatten_cons, List.flatMap_append, List.map_cons, ih]
  rw [h, List.map_ofFn]
  rfl

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- If a cuspidal class determines its parameter list up to permutation after expanding
each block, then matched families of classes determine the same pooled list up to
permutation after the same expansion. -/
theorem perm_expanded_pooled_parameters_of_matched_classes
    {α : Type uA} {β : Type uB} {k k' : ℕ}
    (HasParameter : PositiveRankCuspidalClass F → List α → Prop)
    (expand : α → List β)
    (unique : ∀ c {d e}, HasParameter c d → HasParameter c e →
      (d.flatMap expand).Perm (e.flatMap expand))
    (c : Fin k → PositiveRankCuspidalClass F) (c' : Fin k' → PositiveRankCuspidalClass F)
    (e : Fin k ≃ Fin k') (hc : ∀ i, c i = c' (e i))
    {d : Fin k → List α} {d' : Fin k' → List α}
    (hd : ∀ i, HasParameter (c i) (d i)) (hd' : ∀ j, HasParameter (c' j) (d' j))
    {L L' : List α} (hL : L.Perm (List.ofFn d).flatten) (hL' : L'.Perm (List.ofFn d').flatten) :
    (L.flatMap expand).Perm (L'.flatMap expand) := by
  refine (hL.flatMap_right expand).trans ?_
  refine List.Perm.trans ?_ (hL'.flatMap_right expand).symm
  rw [flatMap_flatten_ofFn, flatMap_flatten_ofFn, ← Multiset.coe_eq_coe,
    coe_flatten_ofFn, coe_flatten_ofFn]
  exact Fintype.sum_equiv e _ _ fun i =>
    Multiset.coe_eq_coe.mpr (unique (c i) (hd i) (hc i ▸ hd' (e i)))

end Langlands.Automorphic
