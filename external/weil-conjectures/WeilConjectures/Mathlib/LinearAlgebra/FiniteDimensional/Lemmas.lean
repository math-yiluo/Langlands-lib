/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import WeilConjectures.Mathlib.Algebra.Module.Submodule.Defs

/-!
# Finitely many coordinates detect a finite-dimensional space of functions

## Main statements

- `Submodule.exists_finset_injective_funLeft_domRestrict`: a finite-dimensional subspace `V` of
  the function space `ι → K` admits a finite set `s` of coordinates such that restricting to `s`
  is injective on `V`.
-/

@[expose] public section

namespace Submodule

variable {K ι : Type*} [Field K]

/-- **Finite coordinates detect a finite-dimensional sequence space**
(blueprint `lemma-hankel-rank-rationality--1`): a finite-dimensional subspace `V` of
`ι → K` admits a finite set `s ⊆ ι` of coordinates such that `v ↦ (v i)_{i ∈ s}` is injective
on `V`. Choose `s` minimising the dimension of the common kernel in `V` of the coordinates in `s`;
a nonzero vector of that kernel would have a nonzero coordinate `i`, and adding `i` to `s` would
lower the dimension further. -/
theorem exists_finset_injective_funLeft_domRestrict (V : Submodule K (ι → K))
    [FiniteDimensional K V] :
    ∃ s : Finset ι, Function.Injective
      ((LinearMap.funLeft K K ((↑) : s → ι)).domRestrict V) := by
  classical
  let W : Finset ι → Submodule K V := fun s =>
    LinearMap.ker ((LinearMap.funLeft K K ((↑) : s → ι)).domRestrict V)
  have hW : ∀ s (v : V), v ∈ W s ↔ ∀ i ∈ s, (v : ι → K) i = 0 := by
    intro s v
    simp only [W, LinearMap.mem_ker, LinearMap.domRestrict_apply, funext_iff,
      LinearMap.funLeft_apply, Pi.zero_apply, Subtype.forall]
  obtain ⟨s, -, hs⟩ := (measure fun s : Finset ι => Module.finrank K (W s)).wf.has_min
    Set.univ ⟨∅, Set.mem_univ _⟩
  refine ⟨s, LinearMap.ker_eq_bot.1 ((Submodule.eq_bot_iff _).2 fun v hv => ?_)⟩
  by_contra hv0
  obtain ⟨i, hi⟩ : ∃ i, (v : ι → K) i ≠ 0 := by
    by_contra! h
    exact hv0 (Subtype.ext (funext h))
  have hlt : W (insert i s) < W s := by
    refine lt_of_le_of_ne (fun w hw => (hW _ _).2 fun j hj => (hW _ _).1 hw j
      (Finset.mem_insert_of_mem hj)) fun h => hi ?_
    exact (hW _ _).1 (h ▸ (show v ∈ W s from hv)) i (Finset.mem_insert_self _ _)
  exact hs (insert i s) (Set.mem_univ _) (Submodule.finrank_lt_finrank_of_lt hlt)

end Submodule
