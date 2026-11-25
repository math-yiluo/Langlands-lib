/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Retracts of exact functors

A natural retract of a functor between abelian categories which preserves exact short complexes
preserves them too, since a retract of a zero object is zero. In particular a natural retract
of an exact functor is exact.

## Main results

* `CategoryTheory.Functor.map_exact_of_retract`: a natural retract of a functor preserving exact
  short complexes preserves them.
* `CategoryTheory.Functor.exactFunctor_of_retract`: a natural retract of an exact functor is
  exact.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {L Φ : C ⥤ D} [L.PreservesZeroMorphisms] [Φ.PreservesZeroMorphisms]

/-- A natural retract of a functor preserving exact short complexes preserves them: given
```
L ──i──▶ Φ ──r──▶ L
```
with `i ≫ r = 𝟙 L`, if `Φ` maps exact short complexes to exact ones, so does `L`. -/
lemma map_exact_of_retract (i : L ⟶ Φ) (r : Φ ⟶ L) (hir : i ≫ r = 𝟙 L)
    (hΦ : ∀ S : ShortComplex C, S.Exact → (S.map Φ).Exact) (S : ShortComplex C)
    (hS : S.Exact) : (S.map L).Exact := by
  have hΦS := (ShortComplex.exact_iff_isZero_homology _).1 (hΦ S hS)
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h : S.mapNatTrans i ≫ S.mapNatTrans r = 𝟙 _ := by
    ext <;> exact (NatTrans.comp_app i r _).symm.trans (by rw [hir]; rfl)
  rw [← ShortComplex.homologyMap_id, ← h, ShortComplex.homologyMap_comp,
    hΦS.eq_of_src (ShortComplex.homologyMap (S.mapNatTrans r)) 0, comp_zero]

/-- A natural retract of an exact functor between abelian categories is exact. -/
lemma exactFunctor_of_retract [L.Additive] (i : L ⟶ Φ) (r : Φ ⟶ L) (hir : i ≫ r = 𝟙 L)
    (hΦ : exactFunctor C D Φ) : exactFunctor C D L := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1 hΦ
  have : Φ.PreservesHomology := inferInstance
  have hL := map_exact_of_retract i r hir fun S hS ↦ hS.map Φ
  have : L.PreservesHomology := preservesHomology_of_map_exact L hL
  exact (exactFunctor_iff _).2
    ⟨preservesFiniteLimits_of_preservesHomology _, preservesFiniteColimits_of_preservesHomology _⟩

end CategoryTheory.Functor
