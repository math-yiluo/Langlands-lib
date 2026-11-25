/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# Flat objects of `ModuleCat R`

Let `R` be a commutative ring. An object `M` of `ModuleCat R` is flat in the sense of
`CategoryTheory.ObjectProperty.flat` (tensoring with `M` is exact) if and only if it is a flat
`R`-module (`Module.Flat`).

## Main results

- `ModuleCat.flat_iff_flat`: the two notions of flatness agree.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- An object of `ModuleCat R` is flat, that is tensoring with it is exact, if and only if it is
a flat `R`-module. Tensoring is always right exact, so both say that tensoring with `M`
preserves injective maps. -/
lemma flat_iff_flat (M : ModuleCat.{u} R) : ObjectProperty.flat M ↔ Module.Flat R M := by
  constructor
  · intro hM
    have := (ObjectProperty.flat_iff_preservesFiniteLimits M).1 hM
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{u}]
    intro N N' _ _ _ _ f hf
    have : Mono (ofHom f) := (mono_iff_injective _).2 hf
    exact (mono_iff_injective (M ◁ ofHom f)).1 ((tensorLeft M).map_mono (ofHom f))
  · intro hM
    rw [ObjectProperty.flat_iff_preservesFiniteLimits,
      Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
    intro S hS
    have := hS.epi_g
    refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
    exact (mono_iff_injective (M ◁ S.f)).2 (Module.Flat.lTensor_preserves_injective_linearMap
      S.f.hom ((mono_iff_injective _).1 hS.mono_f))

end ModuleCat
