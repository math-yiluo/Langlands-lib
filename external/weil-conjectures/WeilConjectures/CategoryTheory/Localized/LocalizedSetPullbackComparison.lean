/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.Localized.LocalizedSheavesOverRepresentable

/-! # The canonical set-sheaf comparison for localization of a site

Source: Stacks Project, Sites, Tag 03CF; Modules on Sites, Tag 04J0.
(blueprint: lem-weil-pbc-slice-set-pullback-isIso).
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J] (V : D)
  [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]

end CategoryTheory
namespace CategoryTheory
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  (eC : C ≌ E) (eD : D ≌ F)
  (b : R₁ ⋙ eC.functor ≅ eD.functor ⋙ R₂)

end CategoryTheory
namespace CategoryTheory
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  (K : GrothendieckTopology D) (J : GrothendieckTopology C)
  (f : D ⥤ C) [f.IsContinuous K J] (V : D)

private abbrev sy (K : GrothendieckTopology D) (V : D) : Sheaf K (Type u) :=
  (presheafToSheaf K (Type u)).obj (yoneda.obj V)

variable [(Over.post (X := V) f).IsContinuous (K.over V) (J.over (f.obj V))]

private def sliceEquivalence {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) :
    Sheaf (J.over U) (Type u) ≌ Over (sy J U) := by
  have : IsIso (unitTransformation J U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact unitComparison_isIso J U
  have : IsIso (counitTransformation J U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact counitComparison_isIso J U
  exact Equivalence.mk (extensionFunctor J U) (fibreFunctor J U)
    (asIso (unitTransformation J U)) (asIso (counitTransformation J U))

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

end CategoryTheory
namespace CategoryTheory
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J] (V : D)
  [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]

end CategoryTheory
