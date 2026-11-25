/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Pullback
/-! # Testing maps on inverse-image units
Source: Stacks Project, Tags 00YV, 03D2 and 03D3.
(auxiliary; not a blueprint node).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
/-- A specified unit presents a sheaf as the set inverse image.
Source: Stacks Project, Tags 00YV and 03D2.
(auxiliary; not a blueprint node). -/
structure SheafPullbackUnitPresentation (S : Sheaf J (Type u)) (T : Sheaf K (Type u)) where
  unit : S ⟶ (F.sheafPushforwardContinuous (Type u) J K).obj T
  iso : T ≅ (sheafPullback F (Type u) J K).obj S
  equation : ∀ (U : Cᵒᵖ) (x : S.obj.obj U),
    iso.hom.hom.app (F.op.obj U) (unit.hom.app U x) =
      ((sheafAdjunctionContinuous F (Type u) J K).unit.app S).hom.app U x
namespace SheafPullbackUnitPresentation
variable {S S' S'' : Sheaf J (Type u)} {T T' T'' : Sheaf K (Type u)}
/-- Test equality after the unit, using the adjunction hom equivalence.
Source: Stacks Project, Tag 03D3.
(auxiliary; not a blueprint node). -/
theorem hom_ext (p : SheafPullbackUnitPresentation (F := F) S T)
    {Z : Sheaf K (Type u)} (a b : T ⟶ Z)
    (h : ∀ U x, a.hom.app (F.op.obj U) (p.unit.hom.app U x) =
      b.hom.app (F.op.obj U) (p.unit.hom.app U x)) : a = b := by
  apply (cancel_epi p.iso.inv).1
  apply ((sheafAdjunctionContinuous F (Type u) J K).homEquiv S Z).injective
  ext U x
  have hi (x : S.obj.obj U) :
      p.iso.inv.hom.app (F.op.obj U)
        (((sheafAdjunctionContinuous F (Type u) J K).unit.app S).hom.app U x) =
          p.unit.hom.app U x := by
    rw [← p.equation U x]
    exact ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app (F.op.obj U)) p.iso.hom_inv_id) _
  change a.hom.app (F.op.obj U) (p.iso.inv.hom.app (F.op.obj U) _) = _
  exact (congrArg (fun y ↦ a.hom.app (F.op.obj U) y) (hi x)).trans
    ((h U x).trans (congrArg (fun y ↦ b.hom.app (F.op.obj U) y) (hi x).symm))
/-- Product presentations use the inverse binary-product comparison.
Source: Stacks Project, Tags 00YV and 03D2.
(auxiliary; not a blueprint node).
Proof: finite-limit preservation makes the product comparison an isomorphism.
The two projections of its unit equation are exactly naturality of the unit at
both source projections, followed by the two given unit equations. -/
noncomputable def tensor [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (p : SheafPullbackUnitPresentation (F := F) S T)
    (q : SheafPullbackUnitPresentation (F := F) S' T') :
    SheafPullbackUnitPresentation (F := F) (S ⊗ S') (T ⊗ T') where
  unit := p.unit ⊗ₘ q.unit
  iso := (MonoidalCategory.tensorIso p.iso q.iso) ≪≫
    (CartesianMonoidalCategory.prodComparisonIso
      (sheafPullback F (Type u) J K) S S').symm
  equation := by
    intro U x
    let L := sheafPullback F (Type u) J K
    let e := CartesianMonoidalCategory.prodComparisonIso L S S'
    apply injective_of_mono (e.hom.hom.app (F.op.obj U))
    have he : ((e.hom.hom.app (F.op.obj U))
        (((sheafAdjunctionContinuous F (Type u) J K).unit.app (S ⊗ S')).hom.app U x)) =
        (((sheafAdjunctionContinuous F (Type u) J K).unit.app S).hom.app U x.1,
          ((sheafAdjunctionContinuous F (Type u) J K).unit.app S').hom.app U x.2) := by
      apply Prod.ext
      · have hn := (sheafAdjunctionContinuous F (Type u) J K).unit.naturality
          (CartesianMonoidalCategory.fst S S')
        have hp := CartesianMonoidalCategory.prodComparison_fst L S S'
        have h := congrArg (fun z ↦ z.hom.app (F.op.obj U)) hp
        have h' := congrArg (fun z ↦ z.hom.app U) hn
        exact (ConcreteCategory.congr_hom h _).trans
          (ConcreteCategory.congr_hom h' x).symm
      · have hn := (sheafAdjunctionContinuous F (Type u) J K).unit.naturality
          (CartesianMonoidalCategory.snd S S')
        have hp := CartesianMonoidalCategory.prodComparison_snd L S S'
        have h := congrArg (fun z ↦ z.hom.app (F.op.obj U)) hp
        have h' := congrArg (fun z ↦ z.hom.app U) hn
        exact (ConcreteCategory.congr_hom h _).trans
          (ConcreteCategory.congr_hom h' x).symm
    change e.hom.hom.app (F.op.obj U) (e.inv.hom.app (F.op.obj U)
      (p.iso.hom.hom.app (F.op.obj U) (p.unit.hom.app U x.1),
        q.iso.hom.hom.app (F.op.obj U) (q.unit.hom.app U x.2))) = _
    have he0 := congrArg (fun z ↦ z.hom.app (F.op.obj U)) e.inv_hom_id
    have hei := ConcreteCategory.congr_hom he0
      (show (L.obj S ⊗ L.obj S').obj.obj (F.op.obj U) from
        (p.iso.hom.hom.app (F.op.obj U) (p.unit.hom.app U x.1),
        q.iso.hom.hom.app (F.op.obj U) (q.unit.hom.app U x.2)))
    exact hei.trans ((congrArg₂ Prod.mk (p.equation U x.1) (q.equation U x.2)).trans he.symm)
/-- Transport an operation through presentations.
Source: Stacks Project, Tag 03D2.
(auxiliary; not a blueprint node). -/
noncomputable def map (p : SheafPullbackUnitPresentation (F := F) S T)
    (q : SheafPullbackUnitPresentation (F := F) S' T') (a : S ⟶ S') : T ⟶ T' :=
  p.iso.hom ≫ (sheafPullback F (Type u) J K).map a ≫ q.iso.inv
/-- Transported operations agree with their source on unit sections.
Source: Stacks Project, Tag 03D2.
(auxiliary; not a blueprint node). -/
theorem map_unit (p : SheafPullbackUnitPresentation (F := F) S T)
    (q : SheafPullbackUnitPresentation (F := F) S' T') (a : S ⟶ S')
    (U : Cᵒᵖ) (x : S.obj.obj U) :
    (p.map q a).hom.app (F.op.obj U) (p.unit.hom.app U x) =
      q.unit.hom.app U (a.hom.app U x) := by
  change q.iso.inv.hom.app (F.op.obj U)
    (((sheafPullback F (Type u) J K).map a).hom.app (F.op.obj U)
      (p.iso.hom.hom.app (F.op.obj U) (p.unit.hom.app U x))) = _
  rw [p.equation]
  have hn := (sheafAdjunctionContinuous F (Type u) J K).unit.naturality a
  have hz := congrArg (fun z ↦ z.hom.app U) hn
  have hn' := ConcreteCategory.congr_hom hz x
  change _ = ((sheafPullback F (Type u) J K).map a).hom.app (F.op.obj U) _ at hn'
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app (F.op.obj U)) q.iso.hom_inv_id)
    (q.unit.hom.app U (a.hom.app U x))
  exact (congrArg (fun y ↦ q.iso.inv.hom.app (F.op.obj U) y) hn'.symm).trans
    ((congrArg (fun y ↦ q.iso.inv.hom.app (F.op.obj U) y)
      (q.equation U (a.hom.app U x)).symm).trans hi)
end SheafPullbackUnitPresentation
end CategoryTheory
