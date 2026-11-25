/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Zero objects of algebras with invertible structure morphism

For an endofunctor `F` of a category `C`, an object `(a, φ : F a ≅ a)` of `IsoAlgebra F` is a zero
object as soon as `a` is one; conversely, if `C` has a zero object and `F` preserves zero
morphisms, the underlying object of a zero object of `IsoAlgebra F` is zero.

## Main results

- `CategoryTheory.Endofunctor.IsoAlgebra.isZero_mk`
- `CategoryTheory.Endofunctor.IsoAlgebra.carrier_isZero`
-/

@[expose] public section

open CategoryTheory Limits

open scoped ZeroObject

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category C] {F : C ⥤ C}

/-- An algebra with invertible structure morphism whose underlying object is zero is a zero
object. -/
lemma isZero_mk {a : C} (ha : IsZero a) (Φ : F.obj a ≅ a) : IsZero (mk a Φ) where
  unique_to Y := ⟨⟨⟨ObjectProperty.homMk ⟨ha.to_ Y.carrier, (ha.of_iso Φ).eq_of_src _ _⟩⟩,
    fun _ ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (ha.eq_of_src _ _))⟩⟩
  unique_from Y := ⟨⟨⟨ObjectProperty.homMk ⟨ha.from_ Y.carrier, ha.eq_of_tgt _ _⟩⟩,
    fun _ ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (ha.eq_of_tgt _ _))⟩⟩

/-- The underlying object of a zero algebra with invertible structure morphism is zero, for an
endofunctor preserving zero morphisms of a category with a zero object. -/
lemma carrier_isZero [HasZeroMorphisms C] [HasZeroObject C] [F.PreservesZeroMorphisms]
    {K : IsoAlgebra F} (hK : IsZero K) : IsZero K.carrier :=
  (isZero_zero C).of_iso ((forget F).mapIso
    (hK.iso (isZero_mk (isZero_zero C) (F.map_isZero (isZero_zero C)).isoZero)))

end CategoryTheory.Endofunctor.IsoAlgebra
