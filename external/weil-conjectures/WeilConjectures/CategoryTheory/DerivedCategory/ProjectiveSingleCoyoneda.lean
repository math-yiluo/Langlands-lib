/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Shifted morphisms out of `P[0]` for a projective object `P`

Let `P` be a projective object of an abelian category `C`. The bijection
`(P[0] ⟶ X) ≃ (P ⟶ H⁰(X))` of `DerivedCategory.singleFunctorZeroHomEquiv` is natural in `X` and
additive, and after shifting it identifies the functor `X ↦ Hom(P[0], X⟦n⟧)` with
`X ↦ Hom(P, Hⁿ(X))`, both on the derived category and on the bounded below derived category.

## Main definitions

- `DerivedCategory.preadditiveCoyonedaObjSingleFunctorZeroIso`: `Hom(P[0], -) ≅ Hom(P, H⁰(-))`.
- `DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso`:
  `Hom(P[0], -⟦n⟧) ≅ Hom(P, Hⁿ(-))`.
- `DerivedCategory.Plus.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso`: the same on
  `DerivedCategory.Plus C`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]

/-- For a projective object `P`, taking `H⁰` identifies the functor `X ↦ Hom(P[0], X)` to abelian
groups with `X ↦ Hom(P, H⁰(X))`. -/
noncomputable def preadditiveCoyonedaObjSingleFunctorZeroIso (P : C) [Projective P] :
    preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj P)) ≅
      homologyFunctor C 0 ⋙ preadditiveCoyoneda.obj (op P) :=
  NatIso.ofComponents
    (fun X ↦ (AddEquiv.mk' (singleFunctorZeroHomEquiv P X) (fun f g ↦ by
      simp [Preadditive.comp_add])).toAddCommGrpIso)
    (fun g ↦ by
      ext f
      exact (congrArg (_ ≫ ·) ((homologyFunctor C 0).map_comp f g)).trans
        (Category.assoc _ _ _).symm)

/-- For a projective object `P`, the functor `X ↦ Hom(P[0], X⟦n⟧)` to abelian groups is
`X ↦ Hom(P, Hⁿ(X))`. -/
noncomputable def shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso (P : C)
    [Projective P] (n : ℤ) :
    shiftFunctor (DerivedCategory C) n ⋙ preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj P)) ≅
      homologyFunctor C n ⋙ preadditiveCoyoneda.obj (op P) :=
  Functor.isoWhiskerLeft _ (preadditiveCoyonedaObjSingleFunctorZeroIso P) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((homologyFunctor C 0).isoShift n) _

namespace Plus

/-- For a projective object `P`, the functor `X ↦ Hom(P[0], X⟦n⟧)` on the bounded below derived
category is `X ↦ Hom(P, Hⁿ(X))`. -/
noncomputable def shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso (P : C)
    [Projective P] (n : ℤ) :
    shiftFunctor (Plus C) n ⋙ preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj P)) ≅
      homologyFunctor C n ⋙ preadditiveCoyoneda.obj (op P) :=
  Functor.isoWhiskerLeft _
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.preadditiveCoyonedaObjIso _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Plus.ι.commShiftIso n) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Plus.ι
      (DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso P n) ≪≫
    (Functor.associator _ _ _).symm

end Plus

end DerivedCategory
