/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Extending statements from a property of objects to its localizing closure

Let `C` be a pretriangulated category and `P : ObjectProperty C`, with localizing closure
`Loc(P) = P.localizingClosure` (`WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure`).
The arguments of the blueprint which extend a statement from `P` to `Loc(P)` ("the objects
satisfying it form a localizing subcategory containing `P`") are collected here. They only need
the functors involved to be triangulated and to preserve the coproducts of objects of `Loc(P)`
(`CategoryTheory.Functor.PreservesCoproductsOn`), not all coproducts: for instance the proper
direct image preserves direct sums on `Loc(Dctf)` but not on the whole derived category.

## Main results

- `CategoryTheory.NatTrans.isIso_app_of_localizingClosure` (blueprint
  `lemma-checking-isomorphisms-constructible-complexes--1`): a natural transformation of
  triangulated functors, compatible with the shifts, between functors preserving the coproducts of
  objects of `Loc(P)`, which is an isomorphism on the objects of `P`, is an isomorphism on `Loc(P)`.
- `CategoryTheory.NatTrans.isIso_app_app_of_localizingClosure`: the same in two variables, for
  natural transformations of bifunctors (the argument of the projection formula).
- `CategoryTheory.ObjectProperty.localizingClosure_map`: a triangulated functor preserving the
  coproducts of objects of `Loc(P)` and mapping `P` into `Loc(Q)` maps `Loc(P)` into `Loc(Q)`.
- `CategoryTheory.ObjectProperty.localizingClosure_map₂`: the same for bifunctors which are
  triangulated and preserve coproducts in each variable (the argument of the tensor closure).
-/

@[expose] public section

universe w

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace Functor

variable {C D : Type*} [Category* C] [Category* D]

/-- A functor `F : C ⥤ D` *preserves the coproducts of objects of `P`* if it sends every colimit
cocone of a diagram `K : Discrete J ⥤ C`, `J : Type w`, whose objects satisfy `P`, to a colimit
cocone. -/
def PreservesCoproductsOn (F : C ⥤ D) (P : ObjectProperty C) : Prop :=
  ∀ ⦃J : Type w⦄ ⦃K : Discrete J ⥤ C⦄ (c : Cocone K), IsColimit c → (∀ j, P (K.obj j)) →
    Nonempty (IsColimit (F.mapCocone c))

/-- A functor preserving all coproducts indexed by `Type w` preserves the coproducts of objects
of any `P`. -/
lemma preservesCoproductsOn_of_preservesColimitsOfShape (F : C ⥤ D)
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F] (P : ObjectProperty C) :
    F.PreservesCoproductsOn.{w} P :=
  fun _ _ _ hc _ ↦ ⟨isColimitOfPreserves F hc⟩

lemma PreservesCoproductsOn.of_le {F : C ⥤ D} {P Q : ObjectProperty C}
    (h : F.PreservesCoproductsOn.{w} Q) (hPQ : P ≤ Q) : F.PreservesCoproductsOn.{w} P :=
  fun _ _ c hc hK ↦ h c hc (fun j ↦ hPQ _ (hK j))

/-- A functor isomorphic to a functor preserving the coproducts of objects of `P` preserves
them. -/
lemma PreservesCoproductsOn.of_iso {F G : C ⥤ D} {P : ObjectProperty C}
    (h : F.PreservesCoproductsOn.{w} P) (e : F ≅ G) : G.PreservesCoproductsOn.{w} P := by
  intro J K c hc hK
  obtain ⟨h'⟩ := h c hc hK
  exact ⟨IsColimit.mapCoconeEquiv e h'⟩

/-- The composite of functors preserving the coproducts of objects of `P`, resp. `Q`, preserves
the coproducts of objects of `P` if the first one maps `P` into `Q`. -/
lemma PreservesCoproductsOn.comp {E : Type*} [Category* E] {F : C ⥤ D} {G : D ⥤ E}
    {P : ObjectProperty C} {Q : ObjectProperty D} (hF : F.PreservesCoproductsOn.{w} P)
    (hG : G.PreservesCoproductsOn.{w} Q) (hPQ : ∀ X, P X → Q (F.obj X)) :
    (F ⋙ G).PreservesCoproductsOn.{w} P := by
  intro J K c hc hK
  obtain ⟨h⟩ := hF c hc hK
  obtain ⟨h'⟩ := hG (F.mapCocone c) h (fun j ↦ hPQ _ (hK j))
  exact ⟨h'⟩

end Functor

variable {C D : Type*} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category.{w} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace ObjectProperty

/-- A triangulated functor `F : C ⥤ D` which preserves the coproducts of objects of `Loc(P)` and
maps the objects of `P` into `Loc(Q)` maps `Loc(P)` into `Loc(Q)`: the objects `X` of `Loc(P)`
with `F X ∈ Loc(Q)` form a localizing property containing `P`. -/
lemma localizingClosure_map (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] (hF : F.PreservesCoproductsOn.{w} P.localizingClosure)
    (h : ∀ X, P X → Q.localizingClosure (F.obj X)) {X : C}
    (hX : P.localizingClosure X) : Q.localizingClosure (F.obj X) := by
  let R := P.localizingClosure ⊓ (Q.localizingClosure).inverseImage F
  have : R.IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete J :=
        { colimitsOfShape_le := by
            rintro Y ⟨h⟩
            have hY : P.localizingClosure Y :=
              (P.localizingClosure).prop_of_isColimit h.isColimit
                (fun j ↦ (h.prop_diag_obj j).1)
            obtain ⟨hc⟩ := hF _ h.isColimit (fun j ↦ (h.prop_diag_obj j).1)
            exact ⟨hY, (Q.localizingClosure).prop_of_isColimit hc
              (fun j ↦ (h.prop_diag_obj j).2)⟩ } }
  exact (localizingClosure_le (P := P) (Q := R)
    (fun Y hY ↦ ⟨le_localizingClosure P Y hY, h Y hY⟩) X hX).2

variable {C' : Type*} [Category.{w} C'] [HasZeroObject C'] [HasShift C' ℤ] [Preadditive C']
  [∀ (n : ℤ), (shiftFunctor C' n).Additive] [Pretriangulated C']

/-- A bifunctor `T : C ⥤ C' ⥤ D` which is triangulated and preserves the coproducts of objects
of the localizing closures in each variable, and maps `P × P'` into `Loc(Q)`, maps
`Loc(P) × Loc(P')` into `Loc(Q)`. First fix `Y` in `P'` and argue in the first variable, then
fix `X` in `Loc(P)` and argue in the second variable. -/
lemma localizingClosure_map₂ (P : ObjectProperty C) (P' : ObjectProperty C')
    (Q : ObjectProperty D) (T : C ⥤ C' ⥤ D) [∀ X, (T.obj X).CommShift ℤ]
    [∀ X, (T.obj X).IsTriangulated] [∀ Y, (T.flip.obj Y).CommShift ℤ]
    [∀ Y, (T.flip.obj Y).IsTriangulated]
    (h₁ : ∀ Y, P' Y → (T.flip.obj Y).PreservesCoproductsOn.{w} P.localizingClosure)
    (h₂ : ∀ X, P.localizingClosure X →
      (T.obj X).PreservesCoproductsOn.{w} P'.localizingClosure)
    (h : ∀ X Y, P X → P' Y → Q.localizingClosure ((T.obj X).obj Y)) {X : C} {Y : C'}
    (hX : P.localizingClosure X) (hY : P'.localizingClosure Y) :
    Q.localizingClosure ((T.obj X).obj Y) :=
  localizingClosure_map P' Q (T.obj X) (h₂ X hX)
    (fun Y' hY' ↦ localizingClosure_map P Q (T.flip.obj Y') (h₁ Y' hY')
      (fun X' hX' ↦ h X' Y' hX' hY') hX) hY

end ObjectProperty

namespace NatTrans

variable {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₁.IsTriangulated]
  [F₂.IsTriangulated] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ]

/-- Blueprint `lemma-checking-isomorphisms-constructible-complexes--1`, for the localizing closure:
let `τ : F₁ ⟶ F₂` be a natural transformation of triangulated functors, compatible with the shifts,
where `F₁` and `F₂` preserve the coproducts of objects of `Loc(P)`. If `τ` is an isomorphism on the
objects of `P`, it is an isomorphism on the objects of `Loc(P)`: the objects of `Loc(P)` on which
`τ` is an isomorphism form a localizing property containing `P`. -/
theorem isIso_app_of_localizingClosure {P : ObjectProperty C}
    (hF₁ : F₁.PreservesCoproductsOn.{w} P.localizingClosure)
    (hF₂ : F₂.PreservesCoproductsOn.{w} P.localizingClosure)
    (h : ∀ X, P X → IsIso (τ.app X)) {X : C} (hX : P.localizingClosure X) :
    IsIso (τ.app X) := by
  let R := P.localizingClosure ⊓ τ.isoLocus
  have : R.IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete J :=
        { colimitsOfShape_le := by
            rintro Y ⟨h⟩
            have hY : P.localizingClosure Y :=
              (P.localizingClosure).prop_of_isColimit h.isColimit
                (fun j ↦ (h.prop_diag_obj j).1)
            obtain ⟨h₁⟩ := hF₁ _ h.isColimit (fun j ↦ (h.prop_diag_obj j).1)
            obtain ⟨h₂⟩ := hF₂ _ h.isColimit (fun j ↦ (h.prop_diag_obj j).1)
            refine ⟨hY, ?_⟩
            have (j : _) : IsIso (τ.app (h.diag.obj j)) := (h.prop_diag_obj j).2
            let e : h.diag ⋙ F₁ ≅ h.diag ⋙ F₂ :=
              NatIso.ofComponents (fun j ↦ asIso (τ.app (h.diag.obj j)))
                (fun f ↦ τ.naturality _)
            have he : τ.app Y = (h₁.coconePointsIsoOfNatIso h₂ e).hom :=
              h₁.hom_ext fun j ↦ by
                rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
                simp [e]
            rw [isoLocus_iff, he]
            infer_instance } }
  exact (ObjectProperty.localizingClosure_le (P := P) (Q := R)
    (fun Y hY ↦ ⟨ObjectProperty.le_localizingClosure P Y hY, h Y hY⟩) X hX).2

variable {C' : Type*} [Category.{w} C'] [HasZeroObject C'] [HasShift C' ℤ] [Preadditive C']
  [∀ (n : ℤ), (shiftFunctor C' n).Additive] [Pretriangulated C']

/-- The two-variable version of `CategoryTheory.NatTrans.isIso_app_of_localizingClosure`: let
`τ : T₁ ⟶ T₂` be a natural transformation of bifunctors `C ⥤ C' ⥤ D` which are triangulated in
each variable, with `τ` compatible with the shifts in each variable, and with `T₁`, `T₂`
preserving the coproducts of objects of the localizing closures in each variable. If `τ` is an
isomorphism on `P × P'`, it is an isomorphism on `Loc(P) × Loc(P')`. First fix `Y` in `P'` and
argue in the first variable, then fix `X` in `Loc(P)` and argue in the second variable. -/
theorem isIso_app_app_of_localizingClosure {T₁ T₂ : C ⥤ C' ⥤ D} (τ : T₁ ⟶ T₂)
    [∀ X, (T₁.obj X).CommShift ℤ] [∀ X, (T₁.obj X).IsTriangulated]
    [∀ X, (T₂.obj X).CommShift ℤ] [∀ X, (T₂.obj X).IsTriangulated]
    [∀ Y, (T₁.flip.obj Y).CommShift ℤ] [∀ Y, (T₁.flip.obj Y).IsTriangulated]
    [∀ Y, (T₂.flip.obj Y).CommShift ℤ] [∀ Y, (T₂.flip.obj Y).IsTriangulated]
    [∀ X, NatTrans.CommShift (τ.app X) ℤ]
    [∀ Y, NatTrans.CommShift (NatTrans.flipApp τ Y) ℤ]
    {P : ObjectProperty C} {P' : ObjectProperty C'}
    (h₁ : ∀ Y, P' Y → (T₁.flip.obj Y).PreservesCoproductsOn.{w} P.localizingClosure)
    (h₂ : ∀ Y, P' Y → (T₂.flip.obj Y).PreservesCoproductsOn.{w} P.localizingClosure)
    (h₃ : ∀ X, P.localizingClosure X →
      (T₁.obj X).PreservesCoproductsOn.{w} P'.localizingClosure)
    (h₄ : ∀ X, P.localizingClosure X →
      (T₂.obj X).PreservesCoproductsOn.{w} P'.localizingClosure)
    (h : ∀ X Y, P X → P' Y → IsIso ((τ.app X).app Y)) {X : C} {Y : C'}
    (hX : P.localizingClosure X) (hY : P'.localizingClosure Y) :
    IsIso ((τ.app X).app Y) :=
  isIso_app_of_localizingClosure (τ.app X) (h₃ X hX) (h₄ X hX)
    (fun Y' hY' ↦ isIso_app_of_localizingClosure (NatTrans.flipApp τ Y')
      (h₁ Y' hY') (h₂ Y' hY') (fun X' hX' ↦ h X' Y' hX' hY') hX) hY

end NatTrans

end CategoryTheory
