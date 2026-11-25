/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# Atoms of the lattice of Lie submodules are irreducible

An atom `N` of the lattice of Lie submodules of `M` is an irreducible Lie module.
-/

@[expose] public section

open LieModule

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]

/-- An atom of the lattice of Lie submodules of `M` is an irreducible Lie module. -/
lemma isIrreducible_of_isAtom {N : LieSubmodule R L M} (hN : IsAtom N) : IsIrreducible R L N := by
  have : Nontrivial N := (nontrivial_iff_ne_bot R L M).mpr hN.1
  refine IsIrreducible.mk fun P hP ↦ ?_
  let e := mapOrderEmbedding (f := N.incl) Subtype.coe_injective
  have hbot : e ⊥ = ⊥ := map_bot
  have htop : e ⊤ = N := map_incl_top N
  refine e.injective ?_
  rw [htop]
  refine (hN.le_iff.mp map_incl_le).resolve_left fun h ↦ hP (e.injective ?_)
  rw [hbot]
  exact h

end LieSubmodule
