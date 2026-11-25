/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Basic

/-!
# Reindexing exact couples

An exact couple indexed by an additive group `κ` can be reindexed along an additive equivalence
`e : κ ≃+ κ'`: the reindexed couple has objects `D (e.symm i)`, `E (e.symm i)` and its
structure maps have degrees `e a`, `e b`, `e c`. This is used to pass between different
bigradings of the same couple, for instance from the indexing `(q, n)` of the couple of a tower
of distinguished triangles to the indexing `(p, n) = (n - q, n)` by filtration degree and total
degree used in `WeilConjectures/Algebra/Homology/ExactCouple/Convergence.lean`.

## Main definitions

- `CategoryTheory.ExactCouple.reindex`: the reindexing of an exact couple along an additive
  equivalence.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits

namespace CategoryTheory

namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type w} {κ' : Type w'}
  [AddCommGroup κ] [AddCommGroup κ'] {a b c : κ} (X : ExactCouple C a b c)

/-- For an additive equivalence `e`, `e.symm i + x = e.symm j` iff `i + e x = j`. -/
lemma _root_.AddEquiv.symm_add_eq_symm_iff (e : κ ≃+ κ') (i j : κ') (x : κ) :
    e.symm i + x = e.symm j ↔ i + e x = j := by
  constructor
  · intro h
    rw [← e.apply_symm_apply j, ← h, map_add, e.apply_symm_apply]
  · intro h
    rw [← h, map_add, e.symm_apply_apply]

/-- The **reindexing** of an exact couple along an additive equivalence `e : κ ≃+ κ'`: the
objects are `D (e.symm i)` and `E (e.symm i)`, and the maps `α`, `f`, `g` have degrees
`a' = e a`, `b' = e b` and `c' = e c`. -/
def reindex (e : κ ≃+ κ') (a' b' c' : κ') (ha : e a = a') (hb : e b = b') (hc : e c = c') :
    ExactCouple C a' b' c' where
  D i := X.D (e.symm i)
  E i := X.E (e.symm i)
  α i j := X.α (e.symm i) (e.symm j)
  f i j := X.f (e.symm i) (e.symm j)
  g i j := X.g (e.symm i) (e.symm j)
  shape_α i j h := X.shape_α _ _ (fun h' ↦ h (by rwa [e.symm_add_eq_symm_iff, ha] at h'))
  shape_f i j h := X.shape_f _ _ (fun h' ↦ h (by rwa [e.symm_add_eq_symm_iff, hb] at h'))
  shape_g i j h := X.shape_g _ _ (fun h' ↦ h (by rwa [e.symm_add_eq_symm_iff, hc] at h'))
  α_g i j k := X.α_g _ _ _
  g_f i j k := X.g_f _ _ _
  f_α i j k := X.f_α _ _ _
  exact_α_g i j k hij hjk := X.exact_α_g _ _ _ (by rwa [e.symm_add_eq_symm_iff, ha])
    (by rwa [e.symm_add_eq_symm_iff, hc])
  exact_g_f i j k hij hjk := X.exact_g_f _ _ _ (by rwa [e.symm_add_eq_symm_iff, hc])
    (by rwa [e.symm_add_eq_symm_iff, hb])
  exact_f_α i j k hij hjk := X.exact_f_α _ _ _ (by rwa [e.symm_add_eq_symm_iff, hb])
    (by rwa [e.symm_add_eq_symm_iff, ha])

variable (e : κ ≃+ κ') (a' b' c' : κ') (ha : e a = a') (hb : e b = b') (hc : e c = c')

/-- The `D`-objects of a reindexed couple. -/
@[simp] lemma reindex_D (i : κ') : (X.reindex e a' b' c' ha hb hc).D i = X.D (e.symm i) := rfl
/-- The `E`-objects of a reindexed couple. -/
@[simp] lemma reindex_E (i : κ') : (X.reindex e a' b' c' ha hb hc).E i = X.E (e.symm i) := rfl
/-- The maps `α` of a reindexed couple. -/
@[simp] lemma reindex_α (i j : κ') :
    (X.reindex e a' b' c' ha hb hc).α i j = X.α (e.symm i) (e.symm j) := rfl
/-- The maps `f` of a reindexed couple. -/
@[simp] lemma reindex_f (i j : κ') :
    (X.reindex e a' b' c' ha hb hc).f i j = X.f (e.symm i) (e.symm j) := rfl
/-- The maps `g` of a reindexed couple. -/
@[simp] lemma reindex_g (i j : κ') :
    (X.reindex e a' b' c' ha hb hc).g i j = X.g (e.symm i) (e.symm j) := rfl

end ExactCouple

end CategoryTheory
