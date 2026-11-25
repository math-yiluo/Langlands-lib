/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
/-! # Testing maps on inverse-image units
Source: Stacks Project, Tags 00YV, 03D2 and 03D3.
(blueprint: lem-pur-signed-line-pullback-unit-presentation).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory.SignedLinePullbackConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
/-- A specified unit presents a sheaf as the set inverse image.
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: def-pur-signed-line-pullback-unit-presentation). -/
structure SheafPullbackUnitPresentation (S : Sheaf J (Type (max u v w))) (T : Sheaf K (Type
  (max u v w))) where
  unit : S ⟶ (F.sheafPushforwardContinuous (Type (max u v w)) J K).obj T
  iso : T ≅ (sheafPullback F (Type (max u v w)) J K).obj S
  equation : ∀ (U : Cᵒᵖ) (x : S.obj.obj U),
    iso.hom.hom.app (F.op.obj U) (unit.hom.app U x) =
      ((sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.app S).hom.app U x
namespace SheafPullbackUnitPresentation
variable {S S' S'' : Sheaf J (Type (max u v w))} {T T' T'' : Sheaf K (Type (max u v w))}
/-- Test equality after the unit, using the adjunction hom equivalence.
Source: Stacks Project, Tag 03D3.
(blueprint: lem-pur-signed-line-pullback-unit-presentation). -/
theorem hom_ext (p : SheafPullbackUnitPresentation (F := F) S T)
    {Z : Sheaf K (Type (max u v w))} (a b : T ⟶ Z)
    (h : ∀ U x, a.hom.app (F.op.obj U) (p.unit.hom.app U x) =
      b.hom.app (F.op.obj U) (p.unit.hom.app U x)) : a = b := by
  apply (cancel_epi p.iso.inv).1
  apply ((sheafAdjunctionContinuous F (Type (max u v w)) J K).homEquiv S Z).injective
  ext U x
  have hi (x : S.obj.obj U) :
      p.iso.inv.hom.app (F.op.obj U)
        (((sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.app S).hom.app U x) =
          p.unit.hom.app U x := by
    rw [← p.equation U x]
    exact ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app (F.op.obj U)) p.iso.hom_inv_id) _
  change a.hom.app (F.op.obj U) (p.iso.inv.hom.app (F.op.obj U) _) = _
  exact (congrArg (fun y ↦ a.hom.app (F.op.obj U) y) (hi x)).trans
    ((h U x).trans (congrArg (fun y ↦ b.hom.app (F.op.obj U) y) (hi x).symm))
/-- Product presentations use the inverse binary-product comparison.
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-pur-signed-line-pullback-unit-presentation).
Proof: finite-limit preservation makes the product comparison an isomorphism.
The two projections of its unit equation are exactly naturality of the unit at
both source projections, followed by the two given unit equations. -/
noncomputable def tensor [PreservesFiniteLimits (sheafPullback F (Type (max u v w)) J K)]
    (p : SheafPullbackUnitPresentation (F := F) S T)
    (q : SheafPullbackUnitPresentation (F := F) S' T') :
    SheafPullbackUnitPresentation (F := F) (S ⊗ S') (T ⊗ T') where
  unit := p.unit ⊗ₘ q.unit
  iso := (MonoidalCategory.tensorIso p.iso q.iso) ≪≫
    (CartesianMonoidalCategory.prodComparisonIso
      (sheafPullback F (Type (max u v w)) J K) S S').symm
  equation := by
    intro U x
    let L := sheafPullback F (Type (max u v w)) J K
    let e := CartesianMonoidalCategory.prodComparisonIso L S S'
    apply injective_of_mono (e.hom.hom.app (F.op.obj U))
    have he : ((e.hom.hom.app (F.op.obj U))
        (((sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.app (S ⊗ S')).hom.app U x)) =
        (((sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.app S).hom.app U x.1,
          ((sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.app S').hom.app U x.2) := by
      apply Prod.ext
      · have hn := (sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.naturality
          (CartesianMonoidalCategory.fst S S')
        have hp := CartesianMonoidalCategory.prodComparison_fst L S S'
        have h := congrArg (fun z ↦ z.hom.app (F.op.obj U)) hp
        have h' := congrArg (fun z ↦ z.hom.app U) hn
        exact (ConcreteCategory.congr_hom h _).trans
          (ConcreteCategory.congr_hom h' x).symm
      · have hn := (sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.naturality
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
(blueprint: lem-pur-signed-line-pullback-unit-presentation). -/
noncomputable def map (p : SheafPullbackUnitPresentation (F := F) S T)
    (q : SheafPullbackUnitPresentation (F := F) S' T') (a : S ⟶ S') : T ⟶ T' :=
  p.iso.hom ≫ (sheafPullback F (Type (max u v w)) J K).map a ≫ q.iso.inv
/-- Transported operations agree with their source on unit sections.
Source: Stacks Project, Tag 03D2.
(blueprint: lem-pur-signed-line-pullback-unit-presentation). -/
theorem map_unit (p : SheafPullbackUnitPresentation (F := F) S T)
    (q : SheafPullbackUnitPresentation (F := F) S' T') (a : S ⟶ S')
    (U : Cᵒᵖ) (x : S.obj.obj U) :
    (p.map q a).hom.app (F.op.obj U) (p.unit.hom.app U x) =
      q.unit.hom.app U (a.hom.app U x) := by
  change q.iso.inv.hom.app (F.op.obj U)
    (((sheafPullback F (Type (max u v w)) J K).map a).hom.app (F.op.obj U)
      (p.iso.hom.hom.app (F.op.obj U) (p.unit.hom.app U x))) = _
  rw [p.equation]
  have hn := (sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.naturality a
  have hz := congrArg (fun z ↦ z.hom.app U) hn
  have hn' := ConcreteCategory.congr_hom hz x
  change _ = ((sheafPullback F (Type (max u v w)) J K).map a).hom.app (F.op.obj U) _ at hn'
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app (F.op.obj U)) q.iso.hom_inv_id)
    (q.unit.hom.app U (a.hom.app U x))
  exact (congrArg (fun y ↦ q.iso.inv.hom.app (F.op.obj U) y) hn'.symm).trans
    ((congrArg (fun y ↦ q.iso.inv.hom.app (F.op.obj U) y)
      (q.equation U (a.hom.app U x)).symm).trans hi)
/-- The constructed inverse image with its adjunction unit is a presentation.
Source: Mathlib's sheaf inverse-image adjunction.
(blueprint: def-pur-signed-line-pullback-unit-presentation). -/
noncomputable def canonical (T : Sheaf J (Type (max u v w))) :
    SheafPullbackUnitPresentation (F := F) T
      ((sheafPullback F (Type (max u v w)) J K).obj T) where
  unit := (sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.app T
  iso := Iso.refl _
  equation _ _ := rfl

/-- Unit-compatible binary operations are preserved on every generalized graph.
Source: Stacks Project, Tag 03D2.
(blueprint: lem-pur-signed-line-unit-presentation-graphs)
Proof: test the two maps from the inverse image of the test sheaf on its unit.
Naturality of that unit and the presentation equations identify all three operands
with their source-unit images. The assumed compatibility reduces the equality to
the source graph equation. The inverse-image adjunction then detects equality. -/
theorem binary_graph
    (p : SheafPullbackUnitPresentation (F := F) S T)
    (q : SheafPullbackUnitPresentation (F := F) S' T')
    (r : SheafPullbackUnitPresentation (F := F) S'' T'')
    (op : ∀ V, S.obj.obj V → S'.obj.obj V → S''.obj.obj V)
    (b : T ⊗ T' ⟶ T'')
    (hu : ∀ V x y, b.hom.app (F.op.obj V)
      (p.unit.hom.app V x, q.unit.hom.app V y) = r.unit.hom.app V (op V x y))
    (Z : Sheaf J (Type (max u v w))) (x : Z ⟶ S) (y : Z ⟶ S') (z : Z ⟶ S'')
    (hz : ∀ V a, z.hom.app V a = op V (x.hom.app V a) (y.hom.app V a)) :
    (sheafPullback F (Type (max u v w)) J K).map z ≫ r.iso.inv =
      CartesianMonoidalCategory.lift
        ((sheafPullback F (Type (max u v w)) J K).map x ≫ p.iso.inv)
        ((sheafPullback F (Type (max u v w)) J K).map y ≫ q.iso.inv) ≫ b := by
  let c := canonical (F := F) (K := K) Z
  change c.map r z =
    CartesianMonoidalCategory.lift (c.map p x) (c.map q y) ≫ b
  apply c.hom_ext
  intro V a
  change (c.map r z).hom.app (F.op.obj V) (c.unit.hom.app V a) =
    b.hom.app (F.op.obj V)
      ((c.map p x).hom.app (F.op.obj V) (c.unit.hom.app V a),
        (c.map q y).hom.app (F.op.obj V) (c.unit.hom.app V a))
  rw [c.map_unit r z, c.map_unit p x, c.map_unit q y, hu, hz]

/-- Unit-compatible constants are preserved on every generalized graph.
Source: Stacks Project, Tag 03D2.
(blueprint: lem-pur-signed-line-unit-presentation-graphs)
Proof: use the same unit test as for binary operations; the target constant
has the prescribed value on all source-unit sections. -/
theorem constant_graph
    (p : SheafPullbackUnitPresentation (F := F) S T)
    (o : ∀ V, S.obj.obj V) (b : 𝟙_ (Sheaf K (Type (max u v w))) ⟶ T)
    (hu : ∀ V, b.hom.app (F.op.obj V) PUnit.unit = p.unit.hom.app V (o V))
    (Z : Sheaf J (Type (max u v w))) (x : Z ⟶ S)
    (hx : ∀ V a, x.hom.app V a = o V) :
    (sheafPullback F (Type (max u v w)) J K).map x ≫ p.iso.inv =
      CartesianMonoidalCategory.toUnit _ ≫ b := by
  let c := canonical (F := F) (K := K) Z
  change c.map p x = _
  apply c.hom_ext
  intro V a
  change (c.map p x).hom.app (F.op.obj V) (c.unit.hom.app V a) =
    b.hom.app (F.op.obj V) PUnit.unit
  rw [c.map_unit p x, hx, hu]

end SheafPullbackUnitPresentation
end CategoryTheory.SignedLinePullbackConstruction
