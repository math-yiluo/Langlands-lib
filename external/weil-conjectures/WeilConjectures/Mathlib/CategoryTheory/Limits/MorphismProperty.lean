/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Flatness of base change and of change of property on slices of a morphism property

The slice `P.Over ⊤ Y` of a category with pullbacks has finite limits and base change
`P.Over ⊤ Y ⥤ P.Over ⊤ X` along an arbitrary morphism `f : X ⟶ Y` preserves them, hence
base change is representably flat
(`CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`). The same holds for the
functor `P.Over ⊤ X ⥤ P'.Over ⊤ X` induced by `P ≤ P'`
(`CategoryTheory.MorphismProperty.Over.representablyFlat_changeProp`).

For a base category with objects in `Type (u + 1)` and `Hom`-types in `Type u` and a
coefficient category `A` with `Hom`-types in `Type (u + 1)`, the pointwise left Kan extensions
of `A`-valued presheaves along the opposite of base change exist by
`CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize`, and they are left
exact (`CategoryTheory.MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty.Over

/-- Base change along an arbitrary morphism `f : X ⟶ Y` is representably flat: the slice
`P.Over ⊤ Y` has finite limits and base change preserves them. -/
instance representablyFlat_pullback {T : Type*} [Category T] [HasPullbacks T]
    (P : MorphismProperty T) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    [P.HasOfPostcompProperty P] {X Y : T} (f : X ⟶ Y) :
    RepresentablyFlat (pullback P ⊤ f) :=
  flat_of_preservesFiniteLimits _

section ChangeProp

variable {T : Type*} [Category T] [HasPullbacks T] {P P' : MorphismProperty T}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [P'.IsMultiplicative] [P'.IsStableUnderBaseChange] [P'.HasOfPostcompProperty P']

/-- For `P ≤ P'`, the functor `P.Over ⊤ X ⥤ P'.Over ⊤ X` preserves finite limits. -/
instance preservesFiniteLimits_changeProp (X : T) (hPP' : P ≤ P') :
    PreservesFiniteLimits (changeProp X hPP' (le_refl (⊤ : MorphismProperty T))) := by
  -- composed with the forgetful functor of `P'.Over ⊤ X`, which reflects finite limits, it is
  -- the forgetful functor of `P.Over ⊤ X`
  have : PreservesFiniteLimits (changeProp X hPP' le_rfl ⋙ Over.forget P' ⊤ X) :=
    inferInstanceAs <| PreservesFiniteLimits (Over.forget P ⊤ X)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Over.forget P' ⊤ X)

/-- For `P ≤ P'`, the functor `P.Over ⊤ X ⥤ P'.Over ⊤ X` is representably flat. -/
instance representablyFlat_changeProp (X : T) (hPP' : P ≤ P') :
    RepresentablyFlat (changeProp X hPP' (le_refl (⊤ : MorphismProperty T))) :=
  flat_of_preservesFiniteLimits _

end ChangeProp

variable {T : Type (u + 1)} [Category.{u} T] [HasPullbacks T]

/-- The presheaf-level left Kan extension along the opposite of base change by an
*arbitrary* morphism `f : X ⟶ Y` is left exact for a Grothendieck abelian coefficient
category `A` with `Hom`-types in `Type (u + 1)`.

Here `[P.HasOfPostcompProperty P]` enters only through `MorphismProperty.Over.hasPullbacks`,
which is what makes `P.Over ⊤ Y` finitely complete and hence base change representably
flat. -/
instance preservesFiniteLimits_op_lan_pullback (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (P : MorphismProperty T) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] {X Y : T} (f : X ⟶ Y) :
    PreservesFiniteLimits ((pullback P ⊤ f).op.lan :
      ((P.Over ⊤ Y)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ X)ᵒᵖ ⥤ A) :=
  -- `preservesFiniteLimits_op_lan_of_flat` at the size `(u, u + 1)` of the indexing comma
  -- categories, where `A` has exact filtered colimits by AB5
  inferInstance

end CategoryTheory.MorphismProperty.Over
