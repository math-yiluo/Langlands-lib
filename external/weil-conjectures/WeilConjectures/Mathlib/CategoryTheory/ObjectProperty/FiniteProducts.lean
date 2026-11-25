/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Closure under finite products of an inverse image

If `P` is a property of objects of `C` closed under finite products and `F : D ⥤ C` preserves
finite products, then `P.inverseImage F` is closed under finite products.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C) (F : D ⥤ C)

instance IsClosedUnderFiniteProducts.inverseImage [P.IsClosedUnderFiniteProducts]
    [PreservesFiniteProducts F] :
    (P.inverseImage F).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape _ _ := inferInstance

end CategoryTheory.ObjectProperty

/-! ### Ported from the `proetale` package
(`Proetale.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts`) -/

universe w

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] {P : ObjectProperty C}

/-- To show `P.IsClosedUnderFiniteProducts`, it suffices to show
`P.IsClosedUnderLimitsOfShape (Discrete J)` for all finite `J` in a single universe. -/
lemma IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape_discrete
    (h : ∀ (J : Type w) [Finite J], P.IsClosedUnderLimitsOfShape (Discrete J)) :
    P.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
    have := h (ULift.{w} (Fin n))
    exact .of_equivalence (Discrete.equivalence (Equiv.ulift.trans e.symm))

end CategoryTheory.ObjectProperty
