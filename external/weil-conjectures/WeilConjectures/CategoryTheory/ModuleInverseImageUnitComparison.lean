/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction

/-! Unit compatibility for module inverse-image comparisons. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
/-- The underlying module inverse image comparison respects the adjunction unit.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(auxiliary; not a blueprint node).
Proof: use the ring and abelian unit presentations to construct the scalar action
on the actual abelian inverse image. Unit generators detect linearity of adjoints.
The restricted adjunction therefore has the abelian unit as its underlying unit.
Uniqueness of left adjoints compares the chosen module pullback with this lift;
the unit equation for that comparison gives the asserted equation. -/
theorem inverseImage_underlying_unit_of_ring_presentation
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M, (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
        (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
          ((toSheaf A).obj M) := by
  exact inverseImage_underlying_of_ring_presentation φ pr hr

end SheafOfModules
