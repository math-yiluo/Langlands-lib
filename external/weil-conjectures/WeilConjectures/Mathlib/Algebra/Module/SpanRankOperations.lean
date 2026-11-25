/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations

/-!
# The embedding dimension of a local ring via a basis of the cotangent space
-/

@[expose] public section

open IsLocalRing

/-- In a noetherian local ring, the cotangent space has dimension the number of elements of any
linearly independent family spanning it. -/
theorem IsLocalRing.spanFinrank_maximalIdeal_eq_ncard {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {b : Set (maximalIdeal R)} (hfin : b.Finite)
    (hb : LinearIndepOn (ResidueField R) (maximalIdeal R).toCotangent b)
    (hspan : Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' b) = ⊤) :
    (maximalIdeal R).spanFinrank = b.ncard := by
  have := (hfin.image (maximalIdeal R).toCotangent).fintype
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← finrank_top, ← hspan,
    finrank_span_set_eq_card hb.id_image, ← Set.ncard_eq_toFinset_card',
    hb.injOn.ncard_image]

end
