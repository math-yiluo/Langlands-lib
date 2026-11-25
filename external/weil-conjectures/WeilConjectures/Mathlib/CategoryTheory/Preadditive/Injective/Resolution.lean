/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Categories with injective resolutions have enough injectives

If every object `X` of `C` has an injective resolution `X ⟶ I⁰ ⟶ I¹ ⟶ ⋯`, then the
monomorphism `X ⟶ I⁰` is an injective presentation of `X`, so `C` has enough injectives.
This is the converse of Mathlib's instance deducing `HasInjectiveResolutions C` from
`EnoughInjectives C` in an abelian category.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroObject C] [HasZeroMorphisms C]

/-- A category in which every object has an injective resolution has enough injectives: the
first map `X ⟶ I⁰` of an injective resolution is a monomorphism into an injective object. -/
lemma enoughInjectives_of_hasInjectiveResolutions [HasInjectiveResolutions C] :
    EnoughInjectives C where
  presentation X :=
    let R := (HasInjectiveResolution.out (Z := X)).some
    ⟨{ J := R.cocomplex.X 0
       f := (HomologicalComplex.singleObjXSelf _ 0 X).inv ≫ R.ι.f 0 }⟩

end CategoryTheory
