/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# `κ`-small limits commute with `κ`-filtered colimits

We show that the limit functor `lim : (K ⥤ Type w) ⥤ Type w` over a category `K` with
`HasCardinalLT (Arrow K) κ` is `κ`-accessible (`CategoryTheory.Functor.isCardinalAccessible_lim`),
i.e. `κ`-small limits of types commute with `κ`-filtered colimits.

More generally, in a category `A` with a `κ`-presentable detector `G`, the limit functor
`lim : (K ⥤ A) ⥤ A` preserves colimits of any `κ`-filtered shape
(`CategoryTheory.preservesColimitsOfShape_lim_of_isDetector`). The variant
`CategoryTheory.preservesColimitsOfShape_lim_of_isSeparator` assumes instead that `A` is balanced
and `G` is a separator.
-/

@[expose] public section

universe w v u u' v'

namespace CategoryTheory

open Limits Opposite

/-- If `HasCardinalLT (Arrow K) κ` with `κ : Cardinal.{w}`, then `Type w` has limits of
shape `K`. -/
lemma hasLimitsOfShape_type_of_hasCardinalLT_arrow {K : Type u'} [Category.{v'} K]
    {κ : Cardinal.{w}} (hK : HasCardinalLT (Arrow K) κ) : HasLimitsOfShape K (Type w) := by
  have := hK.small
  have := small_of_small_arrow.{w} K
  have := locallySmall_of_small_arrow.{w} K
  exact hasLimitsOfShape_of_essentiallySmall K (Type w)

/-- If `HasCardinalLT (Arrow K) κ`, then the limit functor `lim : (K ⥤ Type w) ⥤ Type w` is
`κ`-accessible: `κ`-small limits of types commute with `κ`-filtered colimits. -/
lemma Functor.isCardinalAccessible_lim {K : Type u'} [Category.{v'} K]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (hK : HasCardinalLT (Arrow K) κ) :
    letI := hasLimitsOfShape_type_of_hasCardinalLT_arrow hK
    (lim : (K ⥤ Type w) ⥤ Type w).IsCardinalAccessible κ :=
  letI := hasLimitsOfShape_type_of_hasCardinalLT_arrow hK
  Functor.isCardinalAccessible_of_isLimit _ (isLimitLimConeEvaluation K (Type w)) κ hK

/-- In a category `A` with a `κ`-presentable detector `G`, the limit functor
`lim : (K ⥤ A) ⥤ A` over a category `K` with `HasCardinalLT (Arrow K) κ` preserves
colimits of any `κ`-filtered shape `J`.

The proof uses the square
```
               lim
    (K ⥤ A) ────────▶ A
       │              │
  - ⋙ Hom(G, -)    Hom(G, -)
       ▼              ▼
  (K ⥤ Type v) ───▶ Type v
               lim
```
which commutes up to `preservesLimitNatIso (coyoneda.obj (op G))`. The left, bottom and right
functors preserve `κ`-filtered colimits, and `Hom(G, -)` reflects them. -/
lemma preservesColimitsOfShape_lim_of_isDetector {A : Type u} [Category.{v} A]
    {G : A} (hG : IsDetector G) (κ : Cardinal.{v}) [Fact κ.IsRegular]
    [IsCardinalPresentable G κ]
    (J : Type v) [SmallCategory J] [IsCardinalFiltered J κ] [HasColimitsOfShape J A]
    {K : Type u'} [Category.{v'} K] [HasLimitsOfShape K A] (hK : HasCardinalLT (Arrow K) κ) :
    PreservesColimitsOfShape J (lim : (K ⥤ A) ⥤ A) := by
  have := hasLimitsOfShape_type_of_hasCardinalLT_arrow hK
  have := (Functor.isCardinalAccessible_lim κ hK).preservesColimitOfShape J
  have := preservesColimitsOfShape_of_isCardinalPresentable G κ J
  have : PreservesColimitsOfShape J ((lim : (K ⥤ A) ⥤ A) ⋙ coyoneda.obj (op G)) :=
    preservesColimitsOfShape_of_natIso (preservesLimitNatIso (coyoneda.obj (op G))).symm
  have := (isDetector_iff_reflectsIsomorphisms_coyoneda_obj G).1 hG
  have : ReflectsColimitsOfShape J (coyoneda.obj (op G)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves (lim : (K ⥤ A) ⥤ A)
    (coyoneda.obj (op G))

/-- In a balanced category `A` with a `κ`-presentable separator `G`, the limit functor
`lim : (K ⥤ A) ⥤ A` over a category `K` with `HasCardinalLT (Arrow K) κ` preserves
colimits of any `κ`-filtered shape `J`. -/
lemma preservesColimitsOfShape_lim_of_isSeparator {A : Type u} [Category.{v} A] [Balanced A]
    {G : A} (hG : IsSeparator G) (κ : Cardinal.{v}) [Fact κ.IsRegular]
    [IsCardinalPresentable G κ]
    (J : Type v) [SmallCategory J] [IsCardinalFiltered J κ] [HasColimitsOfShape J A]
    {K : Type u'} [Category.{v'} K] [HasLimitsOfShape K A] (hK : HasCardinalLT (Arrow K) κ) :
    PreservesColimitsOfShape J (lim : (K ⥤ A) ⥤ A) :=
  preservesColimitsOfShape_lim_of_isDetector hG.isDetector κ J hK


end CategoryTheory
