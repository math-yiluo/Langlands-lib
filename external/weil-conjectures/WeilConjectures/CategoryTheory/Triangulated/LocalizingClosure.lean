/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Localizing subcategories and the localizing closure

Let `C` be a pretriangulated category whose `Hom`-types live in `Type v`. A property of objects
`P : ObjectProperty C` is *localizing* (`ObjectProperty.IsLocalizing`) if it is a triangulated
subcategory, closed under isomorphisms and under all coproducts indexed by types in `Type v`
which exist in `C`.

The *localizing closure* `P.localizingClosure` of an arbitrary `P` is the smallest localizing
property containing `P`, the intersection of all localizing properties containing `P`. In the
blueprint it is written `Loc(P)`; it is used with `P = Dctf(X, Λ)` in blueprint
`definition-localizing-subcategory`.

The full subcategory of a localizing property is pretriangulated (by the instances of
`Mathlib.CategoryTheory.Triangulated.Subcategory`), and has all coproducts indexed by `Type v`
if `C` has, computed in `C`.

## Main definitions

- `CategoryTheory.ObjectProperty.IsLocalizing`: localizing properties of objects.
- `CategoryTheory.ObjectProperty.localizingClosure`: the localizing closure `Loc(P)`.

## Main results

- `CategoryTheory.ObjectProperty.le_localizingClosure`: `P ≤ Loc(P)`.
- `CategoryTheory.ObjectProperty.localizingClosure_le`: `Loc(P)` is contained in every localizing
  property containing `P`.
- `CategoryTheory.ObjectProperty.isLocalizing_localizingClosure`: `Loc(P)` is localizing.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A property of objects of a pretriangulated category is *localizing* if it is a triangulated
subcategory which is closed under isomorphisms and under coproducts indexed by types in
`Type v` (the universe of the `Hom`-types). -/
class IsLocalizing (P : ObjectProperty C) : Prop extends P.IsTriangulated,
    P.IsClosedUnderIsomorphisms where
  isClosedUnderColimitsOfShape_discrete (J : Type v) :
    P.IsClosedUnderColimitsOfShape (Discrete J)

attribute [instance] IsLocalizing.isClosedUnderColimitsOfShape_discrete

/-- The everything property is localizing. -/
instance : (⊤ : ObjectProperty C).IsLocalizing where
  exists_zero := ⟨0, isZero_zero C, trivial⟩
  isStableUnderShiftBy _ := ⟨fun _ _ ↦ trivial⟩
  toIsTriangulatedClosed₂ := .mk' fun _ _ _ _ ↦ trivial
  isClosedUnderColimitsOfShape_discrete _ := inferInstance

variable (P : ObjectProperty C)

/-- The *localizing closure* `Loc(P)` of a property of objects `P`: the smallest localizing
property containing `P`. An object lies in `Loc(P)` if it lies in every localizing property
containing `P`. -/
def localizingClosure : ObjectProperty C :=
  fun X ↦ ∀ Q : ObjectProperty C, P ≤ Q → Q.IsLocalizing → Q X

/-- `P` is contained in its localizing closure. -/
lemma le_localizingClosure : P ≤ P.localizingClosure :=
  fun _ hX _ hPQ _ ↦ hPQ _ hX

variable {P} in
/-- The localizing closure of `P` is contained in every localizing property containing `P`. -/
lemma localizingClosure_le {Q : ObjectProperty C} [Q.IsLocalizing] (h : P ≤ Q) :
    P.localizingClosure ≤ Q :=
  fun _ hX ↦ hX Q h inferInstance

/-- The localizing closure is monotone. -/
lemma localizingClosure_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.localizingClosure ≤ Q.localizingClosure :=
  fun _ hX R hQR hR ↦ hX R (h.trans hQR) hR


instance : P.localizingClosure.IsClosedUnderIsomorphisms where
  of_iso e hX Q hPQ hQ := Q.prop_of_iso e (hX Q hPQ hQ)

/-- The localizing closure of `P` is localizing. -/
instance isLocalizing_localizingClosure : P.localizingClosure.IsLocalizing where
  exists_zero := ⟨0, isZero_zero C, fun Q _ _ ↦ Q.prop_of_isZero (isZero_zero C)⟩
  isStableUnderShiftBy n := ⟨fun X hX Q hPQ hQ ↦ Q.le_shift n X (hX Q hPQ hQ)⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ Q hPQ hQ ↦
    Q.ext_of_isTriangulatedClosed₂ T hT (h₁ Q hPQ hQ) (h₃ Q hPQ hQ)
  isClosedUnderColimitsOfShape_discrete J :=
    ⟨fun X hX Q hPQ hQ ↦ Q.colimitsOfShape_le (Discrete J) X
      (colimitsOfShape_monotone _ (fun _ hY ↦ hY Q hPQ hQ) X hX)⟩

/-- A localizing property of a category with coproducts has coproducts, computed in `C`. -/
instance hasCoproducts_fullSubcategory [HasCoproducts.{v} C] (Q : ObjectProperty C)
    [Q.IsLocalizing] : HasCoproducts.{v} Q.FullSubcategory :=
  fun _ ↦ inferInstance

/-- The inclusion of a localizing property preserves coproducts. -/
instance preservesColimitsOfShape_ι [HasCoproducts.{v} C] (Q : ObjectProperty C)
    [Q.IsLocalizing] (J : Type v) : PreservesColimitsOfShape (Discrete J) Q.ι :=
  inferInstance
/-- A localizing property is its own localizing closure. -/
lemma localizingClosure_eq_self [P.IsLocalizing] : P.localizingClosure = P :=
  le_antisymm (localizingClosure_le le_rfl) (le_localizingClosure P)


/-- Blueprint `proposition-proper-direct-image-extension-zero`: a triangulated functor `F : C ⥤ D`
preserving coproducts indexed by `Type v` which maps the objects of `P` into `Loc(P')` maps
`Loc(P)` into `Loc(P')`: the objects `X` with `F X ∈ Loc(P')` form a localizing property. -/
lemma localizingClosure_le_inverseImage {D : Type*} [Category.{v} D] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    (P' : ObjectProperty D) {F : C ⥤ D} [F.CommShift ℤ]
    [F.IsTriangulated] [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    (h : P ≤ P'.localizingClosure.inverseImage F) :
    P.localizingClosure ≤ P'.localizingClosure.inverseImage F := by
  have : (P'.localizingClosure.inverseImage F).IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete J :=
        { colimitsOfShape_le := by
            rintro X ⟨h⟩
            exact P'.localizingClosure.prop_of_isColimit
              (isColimitOfPreserves F h.isColimit) h.prop_diag_obj } }
  exact localizingClosure_le h

end CategoryTheory.ObjectProperty
