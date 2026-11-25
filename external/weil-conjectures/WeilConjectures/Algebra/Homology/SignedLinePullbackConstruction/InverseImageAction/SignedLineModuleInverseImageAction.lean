/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
/-! # Scalar actions on the constructed abelian inverse image
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: def-pur-signed-line-module-inverse-image-action).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules.SignedLinePullbackConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {A : Sheaf J RingCat.{max u v w}} {B : Sheaf K RingCat.{max u v w}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{max u v w} J K).obj B)
  (M : SheafOfModules.{max u v w} A)
/-- An action on the actual abelian inverse image, with semilinear restrictions and unit.
The carrier, additive operations and unit map are fixed, rather than chosen.
Source: Stacks Project, Tags 03D2 and 03D3, lemma-pullback-module and
lemma-adjoint-push-pull-modules.
(blueprint: def-pur-signed-line-module-inverse-image-action). -/
structure InverseImageAction where
  module : ∀ U : Dᵒᵖ, Module (B.obj.obj U)
    (((sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M)).obj.obj U)
  restriction : ∀ {U V : Dᵒᵖ} (i : U ⟶ V) (a : B.obj.obj U)
    (m : ((sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M)).obj.obj U),
    letI := module U
    letI := module V
    ((sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M)).obj.map i (a • m) =
      B.obj.map i a •
        ((sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M)).obj.map i m
  unit_smul : ∀ (U : Cᵒᵖ) (a : A.obj.obj U) (m : M.val.obj U),
    letI := module (F.op.obj U)
    ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
      ((toSheaf A).obj M)).hom.app U (a • m) =
        (show B.obj.obj (F.op.obj U) from φ.hom.app U a) •
          (show ((sheafPullback F AddCommGrpCat.{max u v w} J K).obj
            ((toSheaf A).obj M)).obj.obj (F.op.obj U) from
            ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
              ((toSheaf A).obj M)).hom.app U m)
/-- Regard an action with semilinear restrictions as a sheaf of modules.
Source: Stacks Project, Tag 03D2.
(blueprint: def-pur-signed-line-module-inverse-image-action). -/
noncomputable def InverseImageAction.toModule (a : InverseImageAction φ M) :
    SheafOfModules.{max u v w} B := by
  let T := (sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M)
  letI (U : Dᵒᵖ) : Module (B.obj.obj U) (T.obj.obj U) := a.module U
  exact ⟨PresheafOfModules.ofPresheaf T.obj (fun {_ _} i r m ↦ a.restriction i r m), T.property⟩
/-- The abelian carrier of the action construction is unchanged.
Source: Stacks Project, Tag 03D2.
(blueprint: def-pur-signed-line-module-inverse-image-action). -/
noncomputable def InverseImageAction.underlyingIso (a : InverseImageAction φ M) :
    (toSheaf B).obj a.toModule ≅
      (sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M) := Iso.refl _
end SheafOfModules.SignedLinePullbackConstruction
