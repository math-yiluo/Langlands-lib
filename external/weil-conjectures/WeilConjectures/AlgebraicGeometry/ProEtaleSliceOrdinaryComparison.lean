/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientSliceComparisonData
import all WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction

/-! # Normalized ordinary pro-etale coefficient slice comparison

Source: Hemo--Richarz--Scholbach, Lemma 4.5; Stacks 03CE, 07A4, 08J9, 08JB.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true in
private theorem triangle_sections {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C)
    (a : F ⊣ G) (H : Dᵒᵖ ⥤ Ab.{u}) (V : C) (m : H.obj (op (F.obj V))) :
    H.map (F.map (a.unit.app V)).op (H.map (a.counit.app (F.obj V)).op m) = m := by
  change (H.map (a.counit.app (F.obj V)).op ≫
    H.map (F.map (a.unit.app V)).op) m = m
  have ht : F.map (a.unit.app V) ≫ a.counit.app (F.obj V) = 𝟙 _ :=
    a.left_triangle_components V
  rw [← H.map_comp, ← op_comp, ht, op_id]
  exact congrArg (fun f ↦ f m) (H.map_id (op (F.obj V)))

private theorem comparison_presheaf {X : Scheme.{u}} (U : X.ProEt)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}) :
    delta.presheafIso = restrictionPresheafIso U CommRingCat.{u + 1} := by
  apply Iso.ext
  apply NatTrans.ext
  funext O
  apply NatTrans.ext
  funext V
  rw [delta.coprojection, restrictionPresheafIso_coprojection]

private theorem comparison_unit {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}) :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
    let : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
        (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
    let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
        (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    let a := adj.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
      (ProEt.topology U.left) (ProEt.topology X)
    a.unit.app O ≫ (proEtaleSheafDirectImage U.hom CommRingCat.{u + 1}).map
        (delta.sheafIso.inv.app O) =
      (proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).unit.app O := by
  dsimp only
  apply Sheaf.hom_ext
  rw [inverseImageAdjunction_unit]
  change _ ≫ (proEtaleBaseChange U.hom).op.whiskerLeft
    (delta.sheafIso.inv.app O).hom = _
  rw [delta.sheafIso_inv, comparison_presheaf U delta]
  erw [Functor.whiskerLeft_comp, ← Category.assoc]
  congr 1
  exact Adjunction.unit_leftAdjointUniq_hom_app
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial).op.whiskerLeft
      CommRingCat.{u + 1})
    ((proEtaleBaseChange U.hom).op.lanAdjunction CommRingCat.{u + 1}) O.obj

private theorem coefficient_adjunction_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) {O : C} {B : D} (b : F.obj O ≅ B) :
    (a.unit.app O ≫ G.map b.hom) ≫ G.map b.inv = a.unit.app O := by
  simp only [Category.assoc, ← G.map_comp, b.hom_inv_id, G.map_id]
  exact Category.comp_id _

private theorem coefficient_adjunction_counit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) {O : C} {B : D} (b : F.obj O ≅ B) :
    b.inv ≫ F.map (a.unit.app O ≫ G.map b.hom) ≫ a.counit.app B = 𝟙 B := by
  simp only [F.map_comp, Category.assoc]
  rw [← Functor.comp_map, a.counit.naturality, ← Category.assoc (F.map (a.unit.app O)),
    Functor.id_map]
  rw [a.left_triangle_components O]
  simp

private theorem comparison_coefficients {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}) :
    let b := proEtaleSliceCoefficientIso U O B c delta
    let psi := proEtaleRingDirectImageMap U.hom O B c
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
    Functor.whiskerRight (NatTrans.op adj.counit) O.obj =
        psi.hom ≫ (proEtaleBaseChange U.hom).op.whiskerLeft b.inv.hom ∧
      b.inv.hom ≫ (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).op.whiskerLeft psi.hom ≫
        Functor.whiskerRight (NatTrans.op adj.unit) B.obj = 𝟙 B.obj := by
  let : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let a := adj.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U.left) (ProEt.topology X)
  let G := proEtaleSheafDirectImage U.hom CommRingCat.{u + 1}
  let F := AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1} U.hom U.prop
  let b := proEtaleSliceCoefficientIso U O B c delta
  let psi := proEtaleRingDirectImageMap U.hom O B c
  have hp : psi = a.unit.app O ≫ G.map b.hom := by
    change (proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).unit.app O ≫ G.map c.hom = _
    rw [← comparison_unit U O delta]
    simp only [b, proEtaleSliceCoefficientIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_inv, Functor.map_comp, Category.assoc]
    rfl
  have h₁ : psi ≫ G.map b.inv = a.unit.app O := by
    rw [hp]
    exact coefficient_adjunction_inverse a b
  have h₂ : b.inv ≫ F.map psi ≫ a.counit.app B = 𝟙 B := by
    rw [hp]
    exact coefficient_adjunction_counit a b
  exact ⟨(congrArg (fun f ↦ f.hom) h₁).symm,
    congrArg (fun f ↦ f.hom) h₂⟩

set_option backward.isDefEq.respectTransparency true in
/-- Ordinary module pullback along a site object is restriction followed by the
fixed scalar transport. Source: Stacks 03CE and 03CZ
(auxiliary; not a blueprint node).
Proof: the normalized ring-sheaf comparison intertwines the two adjunction units.
Its adjoint coefficient map therefore satisfies the coefficient unit and counit
identities for composition left adjoint to base change. These identities lift
that site adjunction to modules. Both resulting functors are left adjoint to
the prescribed module direct image, so uniqueness of left adjoints gives the iso.
Evaluate its unit equation on a section and use naturality along the distinguished
index unit. The site adjunction triangle identity gives the section normalization. -/
theorem proEtaleSlice_ordinary_comparison {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}) :
    ∃ i : proEtaleRingModulePullback U.hom O B c ≅
        proEtaleSliceModuleRestriction U O ⋙
          ProEtaleCoefficientSliceComparison.e U O B c delta,
      ∀ (N : proEtaleRingModules X O) (V : U.left.ProEt)
        (m : N.val.obj
          (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
        (i.hom.app N).val.app (op V)
          (proEtaleSlicePullbackSection U O B c N V m) = m := by
  let : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let b := proEtaleSliceCoefficientIso U O B c delta
  let F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  let : F.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom
  let : G.IsContinuous (ProEt.topology X) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  let phi : ((sheafCompose (ProEt.topology U.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B) ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology U.left) (ProEt.topology X)).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) :=
    ⟨Functor.whiskerRight b.inv.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let psi : ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) ⟶
      (G.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology U.left)).obj
        ((sheafCompose (ProEt.topology U.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B) :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap U.hom O B c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have h := comparison_coefficients U O B c delta
  let a := SheafOfModules.pushforwardPushforwardAdj.{u + 1}
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial)
    phi psi (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h.1)
    (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h.2)
  let i := (proEtaleRingModuleAdjunction U.hom O B c).leftAdjointUniq a
  refine ⟨i, ?_⟩
  intro N V m
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let k := (adj.unit.app V).op
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (proEtaleRingModuleAdjunction U.hom O B c) a N
  have hv := congrArg (fun f ↦ f.val.app (op (F.obj V)) m) hu
  change (i.hom.app N).val.app (op (G.obj (F.obj V)))
      (((proEtaleRingModuleAdjunction U.hom O B c).unit.app N).val.app
        (op (F.obj V)) m) = N.val.map (adj.counit.app (F.obj V)).op m at hv
  have hn' := PresheafOfModules.naturality_apply (i.hom.app N).val k
    (((proEtaleRingModuleAdjunction U.hom O B c).unit.app N).val.app
      (op (F.obj V)) m)
  apply hn'.trans
  exact (congrArg (fun x ↦ N.val.map (F.map (adj.unit.app V)).op x) hv).trans
    (triangle_sections F G adj N.val.presheaf V m)

end AlgebraicGeometry.Scheme
