/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Short exact sequences in abelian full subcategories

Let `P` be a property of objects of an abelian category `C` containing zero and closed under
kernels, cokernels and finite products, so that the full subcategory of `P` is abelian. Its
inclusion is exact, so a short complex in the full subcategory is short exact if and only if it
is short exact in `C` (`CategoryTheory.ObjectProperty.shortExact_map_ι_iff`). Consequently an
equivalence between two such full subcategories matches short exact sequences in the ambient
categories (`CategoryTheory.ObjectProperty.shortExact_map_ι_iff_of_equivalence`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C) [P.ContainsZero]
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]

instance : PreservesFiniteLimits P.ι :=
  have := P.preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels P.ι

instance : PreservesFiniteColimits P.ι :=
  have := P.preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- A short complex in an abelian full subcategory is short exact if and only if it is short
exact in the ambient abelian category. -/
lemma shortExact_map_ι_iff (S : ShortComplex P.FullSubcategory) :
    (S.map P.ι).ShortExact ↔ S.ShortExact :=
  ShortExact.shortExact_map_iff P.ι

variable {P} {D : Type*} [Category* D] [Abelian D] {Q : ObjectProperty D} [Q.ContainsZero]
  [Q.IsClosedUnderKernels] [Q.IsClosedUnderCokernels] [Q.IsClosedUnderFiniteProducts]

/-- An equivalence between abelian full subcategories of abelian categories matches short exact
sequences: a short complex `S` of objects of `P` is short exact in `C` if and only if its image
under the equivalence is short exact in `D`. -/
lemma shortExact_map_ι_iff_of_equivalence (e : P.FullSubcategory ≌ Q.FullSubcategory)
    (S : ShortComplex P.FullSubcategory) :
    (S.map P.ι).ShortExact ↔ (S.map (e.functor ⋙ Q.ι)).ShortExact := by
  rw [shortExact_map_ι_iff, ShortComplex.map_comp, shortExact_map_ι_iff,
    ShortExact.shortExact_map_iff e.functor]

end CategoryTheory.ObjectProperty
