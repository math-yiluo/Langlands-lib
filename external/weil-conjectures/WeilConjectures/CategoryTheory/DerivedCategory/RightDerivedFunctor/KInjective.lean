/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

/-!
# The right derived functor on K-injective complexes

If `C` has K-injective resolutions, every object of `DerivedCategory C` is the image
`Q.obj I` of a K-injective complex `I`, and the right derived functor of an additive functor
`F : C ⥤ D` is computed on such a complex by applying `F` termwise:
`R(F)(Q I) ≅ Q (F I)`.

## Main definitions and statements

- `DerivedCategory.exists_iso_Q_obj_of_isKInjective`: every object of the derived category is
  isomorphic to `Q.obj I` for a K-injective complex `I`.
- `CategoryTheory.Functor.rightDerivedFunctorObjQIso`: the isomorphism `R(F)(Q I) ≅ Q (F I)` for
  a K-injective complex `I`.
-/

@[expose] public section

open CategoryTheory Abelian

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]

/-- Every object of the derived category of an abelian category with K-injective resolutions is
isomorphic to the image of a K-injective complex. -/
lemma DerivedCategory.exists_iso_Q_obj_of_isKInjective (M : DerivedCategory C) :
    ∃ (I : CochainComplex C ℤ) (_ : I.IsKInjective), Nonempty (M ≅ Q.obj I) := by
  obtain ⟨L, _, i, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective (Q.objPreimage M)
  exact ⟨L, inferInstance, ⟨(Q.objObjPreimageIso M).symm ≪≫ asIso (Q.map i)⟩⟩

namespace CategoryTheory.Functor

variable (F : C ⥤ D) [F.Additive]

/-- The right derived functor of `F` is computed on a K-injective complex `I` by applying `F`
termwise: `R(F)(Q I) ≅ Q (F I)`. This is the inverse of the unit of the right derived functor
at `I`, which is an isomorphism since `I` is K-injective. -/
noncomputable def rightDerivedFunctorObjQIso (I : CochainComplex C ℤ) [I.IsKInjective] :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj I) :=
  F.rightDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
    (asIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I))).symm ≪≫
    (DerivedCategory.quotientCompQhIso D).app ((F.mapHomologicalComplex _).obj I)

end CategoryTheory.Functor
