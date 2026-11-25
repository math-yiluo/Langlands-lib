/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalizationData
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent

/-!
# The graph map into the compactification sheaf

Source: Stacks Project Tag 0F4L (lemma-shriek-into-star-separated-etale),
and SGA 4 XVII 6.2.11 (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.all false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem graph_baseChange_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {P : D ⥤ E} {S : E ⥤ D}
    {Q : C ⥤ F} {T : F ⥤ C} {V : F ⥤ E} {W : E ⥤ F}
    (a : L ⊣ R) (b : P ⊣ S) (c : Q ⊣ T) (d : V ⊣ W)
    (x : S ⋙ R ≅ W ⋙ T) (M : C) {N : E} (φ : (Q ⋙ V).obj M ⟶ N) :
    a.unit.app M ≫ R.map (b.unit.app (L.obj M)) ≫
        R.map (S.map
          ((((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom.app M ≫ φ)) ≫
        x.hom.app N =
      c.unit.app M ≫ T.map (d.unit.app (Q.obj M) ≫ W.map φ) := by
  have h := Adjunction.homEquiv_naturality_right
    ((a.comp b).ofNatIsoRight x)
    ((((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom.app M) φ
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app] at h
  simp only [Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc] at h ⊢
  simp only [← Functor.comp_map] at h ⊢
  rw [← x.hom.naturality_assoc, ← x.hom.naturality] at h
  exact h

namespace GraphNormalization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : Type (u + 1)) [CommRing A]
  {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] (c : Compactification f)
private noncomputable abbrev sectionMap : U ⟶ pullback c.g f :=
  pullback.lift c.i (𝟙 U) (by simpa using c.comm.symm)
private theorem section_open : IsOpenImmersion (sectionMap f c) := by
  have : IsOpenImmersion (sectionMap f c ≫ pullback.fst c.g f) := by
    simpa only [sectionMap, pullback.lift_fst] using
      (inferInstance : IsOpenImmersion c.i)
  exact FormallyUnramified.isOpenImmersion_of_comp (pullback.fst c.g f) (sectionMap f c)
attribute [local instance] section_open

private theorem section_closed : IsClosedImmersion (sectionMap f c) := by
  have : IsClosedImmersion (sectionMap f c ≫ pullback.snd c.g f) := by
    simpa only [sectionMap, pullback.lift_snd] using
      (inferInstance : IsClosedImmersion (𝟙 U))
  exact IsClosedImmersion.of_comp (sectionMap f c) (pullback.snd c.g f)
attribute [local instance] section_closed

private theorem section_comparison_iso :
    IsIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (sectionMap f c)) :=
  isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range _ _
    (sectionMap f c).isClosedEmbedding.isClosed_range
attribute [local instance] section_comparison_iso

private noncomputable def sectionIso :
    upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f) ⋙
      upperStar (ModuleCat.{u + 1} A) (sectionMap f c) ≅ 𝟭 _ :=
  (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c) (pullback.snd c.g f) (𝟙 U)
    (pullback.lift_snd c.i (𝟙 U) (by simpa using c.comm.symm)).symm).symm ≪≫ upperStarId _ U
attribute [local irreducible] sectionIso
private noncomputable def projection :
    upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f) ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) (sectionMap f c) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (upperStarLowerStarAdjunction _ (sectionMap f c)).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (sectionIso A f c).hom _ ≫ (Functor.leftUnitor _).hom ≫
    (asIso (openImmersionLowerShriekToLowerStar _ (sectionMap f c))).inv
private noncomputable def composition :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) (sectionMap f c) ⋙
      etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst c.g f) inferInstance ≅
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
  (((openImmersionLowerShriekUpperStarAdjunction _ (sectionMap f c)).comp
    (etaleLowerShriekUpperStarAdjunction _ (pullback.fst c.g f) inferInstance)).ofNatIsoRight
      (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c) (pullback.fst c.g f) c.i
        (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).symm).leftAdjointUniq
    (openImmersionLowerShriekUpperStarAdjunction _ c.i)
attribute [local irreducible] projection
  composition
  etaleLowerShriek
  openImmersionLowerShriek
private noncomputable def transfer :
    upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f) ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f) where
  app M := (projection A f c).app M ≫
    (etaleLowerShriekUpperStarAdjunction _ (pullback.fst c.g f) inferInstance).unit.app _ ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f)).map
      ((composition A f c).hom.app M)
  naturality M N φ := by
    simp only [Functor.comp_map, Category.assoc]
    erw [(projection A f c).naturality_assoc]
    erw [← Adjunction.unit_naturality_assoc]
    rw [← Functor.map_comp]
    erw [(composition A f c).hom.naturality]
    simp only [Functor.map_comp, Category.assoc]
attribute [local irreducible] transfer
private theorem transfer_formula
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (transfer A f c).app M =
      (projection A f c).app M ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) (sectionMap f c)).map
          ((openImmersionLowerShriekUpperStarAdjunction _ c.i).unit.app M ≫
            (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c) (pullback.fst c.g f) c.i
              (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M)) ≫
        (openImmersionLowerShriekUpperStarAdjunction _ (sectionMap f c)).counit.app _ := by
  have unit_transfer
      {C D E : Type (u + 2)}
      [Category.{u + 1} C] [Category.{u + 1} D] [Category.{u + 1} E]
      {S : C ⥤ D} {T : D ⥤ C} {V : D ⥤ E} {W : E ⥤ D}
      {J : C ⥤ E} {R : E ⥤ C}
      (s : S ⊣ T) (v : V ⊣ W) (j : J ⊣ R) (t : R ≅ W ⋙ T) (N : C) :
      v.unit.app (S.obj N) ≫ W.map
          ((((s.comp v).ofNatIsoRight t.symm).leftAdjointUniq j).hom.app N) =
        S.map (j.unit.app N ≫ t.hom.app (J.obj N)) ≫
          s.counit.app (W.obj (J.obj N)) := by
    apply (s.homEquiv _ _).injective
    rw [s.homEquiv_unit]
    have h := Adjunction.unit_leftAdjointUniq_hom_app ((s.comp v).ofNatIsoRight t.symm) j N
    simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
      Functor.comp_map, Category.assoc] at h
    have hn := t.inv.naturality
      ((((s.comp v).ofNatIsoRight t.symm).leftAdjointUniq j).hom.app N)
    dsimp only [Functor.comp_map] at hn
    rw [← hn] at h
    have h' := congrArg (fun z => z ≫ t.hom.app (J.obj N)) h
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h'
    have hr := (s.homEquiv _ _).apply_symm_apply (j.unit.app N ≫ t.hom.app (J.obj N))
    rw [Adjunction.homEquiv_counit] at hr
    simpa only [Functor.map_comp, Functor.comp_obj, Functor.id_obj, Category.assoc] using
      h'.trans hr.symm
  have hv := unit_transfer
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (sectionMap f c))
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g f) inferInstance)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
    (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c) (pullback.fst c.g f) c.i
      (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm) M
  simpa only [composition, transfer] using congrArg (fun z => (projection A f c).app M ≫ z) hv
private theorem transfer_toLowerStar
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (transfer A f c).app M ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M) =
      (projection A f c).app M ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) (sectionMap f c)).map
          (inv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.i).counit.app M) ≫
            (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c)
              (pullback.fst c.g f) c.i
                (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app
                ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M)) ≫
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) (sectionMap f c)).counit.app _ := by
  have hunit :
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i).unit.app M ≫
          (upperStar (ModuleCat.{u + 1} A) c.i).map
            ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M) =
        inv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.i).counit.app M) := by
    exact IsIso.eq_inv_of_inv_hom_id
      (unit_map_openImmersionLowerShriekToLowerStar_app_counit
        (ModuleCat.{u + 1} A) c.i M)
  rw [transfer_formula A f c M]
  simp only [Category.assoc]
  have hn := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (sectionMap f c)).counit.naturality
      ((upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f)).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M))
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← hn]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [← Functor.comp_map, ← (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c)
    (pullback.fst c.g f) c.i
      (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.naturality]
  rw [reassoc_of% hunit]

private theorem comparison_at_restriction
    (N : Sheaf (pullback c.g f).smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (sectionMap f c)).app
        ((upperStar (ModuleCat.{u + 1} A) (sectionMap f c)).obj N) =
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (sectionMap f c)).counit.app N ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (sectionMap f c)).unit.app N := by
  apply openImmersionLowerShriek_lowerStar_hom_ext
    (ModuleCat.{u + 1} A) (sectionMap f c)
  simp only [Functor.map_comp, Category.assoc,
    unit_map_openImmersionLowerShriekToLowerStar_app_counit,
    Adjunction.right_triangle_components_assoc,
    Category.comp_id]
  exact (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (sectionMap f c)).left_triangle_components N |>.symm

private theorem section_extension_zero
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B : (pullback c.g f).Etale)
    (h : IsEmpty ((MorphismProperty.Over.pullback @Etale ⊤ (sectionMap f c)).obj B).left) :
    IsZero (((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (sectionMap f c)).obj M).obj.obj (Opposite.op B)) := by
  let e := asIso ((openImmersionLowerShriekToLowerStar
    (ModuleCat.{u + 1} A) (sectionMap f c)).app M)
  let ev := (sheafToPresheaf (pullback c.g f).smallEtaleTopology
    (ModuleCat.{u + 1} A)) ⋙
      (evaluation _ (ModuleCat.{u + 1} A)).obj (Opposite.op B)
  have hz : IsZero (((lowerStar (ModuleCat.{u + 1} A)
      (sectionMap f c)).obj M).obj.obj (Opposite.op B)) :=
    IsZero.of_iso (isZero_zero _) ((Scheme.Etale.isTerminalSectionsOfIsEmpty M
      ((MorphismProperty.Over.pullback @Etale ⊤ (sectionMap f c)).obj B)).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  exact hz.of_iso (ev.mapIso e)

private theorem transfer_toLowerStar_postunit
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (transfer A f c).app M ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (sectionMap f c)).unit.app _ =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (sectionMap f c)).unit.app _ ≫
      (lowerStar (ModuleCat.{u + 1} A) (sectionMap f c)).map
        ((sectionIso A f c).hom.app M ≫
          inv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.i).counit.app M) ≫
          (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c)
            (pullback.fst c.g f) c.i
              (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app
              ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M)) := by
  rw [← Category.assoc, transfer_toLowerStar A f c M]
  simp only [Category.assoc]
  erw [← comparison_at_restriction A f c
    ((upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f)).obj
      ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M))]
  erw [(openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
    (sectionMap f c)).naturality]
  simp only [projection, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id, Category.assoc,
    asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id_assoc, Functor.map_comp]
  erw [Category.id_comp]

private noncomputable def delta :
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⋙
      upperStar (ModuleCat.{u + 1} A) c.g ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
  (etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).hom ≫
    Functor.whiskerRight (projection A f c) _ ≫ (composition A f c).hom
attribute [local irreducible] delta
private theorem transfer_eq (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (transfer A f c).app M =
      ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst c.g f) inferInstance).homEquiv _ _)
        ((etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).inv.app M ≫
          (delta A f c).app M) := by
  simp only [delta, NatTrans.comp_app, Functor.whiskerRight_app,
    Iso.inv_hom_id_app_assoc, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc]
  erw [Adjunction.unit_naturality_assoc]
  with_unfolding_all rfl
set_option maxRecDepth 4000 in
private theorem comparison_unit
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance).unit.app M ≫
        (upperStar (ModuleCat.{u + 1} A) f).map
          ((etaleCompactificationGraphMap A f c).app M) ≫
        (baseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g f).toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd c.g f)).unit.app M ≫
        (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).map
          ((transfer A f c).app M) := by
  have hcomparison : (etaleCompactificationGraphMap A f c).app M =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).homEquiv _ _
        ((delta A f c).app M) := by
    unfold etaleCompactificationGraphMap delta projection composition sectionIso sectionMap
    rfl
  rw [hcomparison, transfer_eq]
  let : ∀ F, IsIso ((baseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq).app F) :=
    fun F => isIso_baseChangeMap_app_of_flat A (IsPullback.of_hasPullback c.g f) F
  let : IsIso (baseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq) := NatIso.isIso_of_isIso_app _
  have h := graph_baseChange_unit
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd c.g f))
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g f) inferInstance)
    (asIso (baseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq)) M
    ((etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).inv.app M ≫
      (delta A f c).app M)
  simp only [etaleLowerShriekBaseChangeIso, Iso.hom_inv_id_app_assoc,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at h ⊢
  exact h

private theorem comparison_restriction_unit
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).unit.app M ≫
        (localizationRestriction (ModuleCat.{u + 1} A) f inferInstance).map
          ((etaleCompactificationGraphMap A f c).app M) ≫
        (localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd c.g f)).unit.app M ≫
        (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).map
          ((transfer A f c).app M ≫
            (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
              (pullback.fst c.g f) inferInstance).hom.app _) := by
  have h := comparison_unit A f c M
  rw [baseChangeMap_flip_eq (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback c.g f).toCommSq.flip] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] at h ⊢
  have h' := congrArg (fun z => z ≫
    (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).map
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
        (pullback.fst c.g f) inferInstance).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M))) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id] at h'
  simp only [Functor.map_comp, Category.assoc] at h'
  rw [← h']
  simp only [etaleLowerShriekRestrictionAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
    f inferInstance).hom.naturality_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Functor.comp_obj]

private noncomputable def normalizedTransfer
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).obj M ⟶
      (localizationRestriction (ModuleCat.{u + 1} A) (pullback.fst c.g f)
        inferInstance).obj ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M) :=
  (transfer A f c).app M ≫
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
      (pullback.fst c.g f) inferInstance).hom.app _ ≫
    (localizationRestriction (ModuleCat.{u + 1} A) (pullback.fst c.g f)
      inferInstance).map ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app M)
attribute [local irreducible] normalizedTransfer

private theorem siteBC_iso :
    IsIso (MorphismProperty.Over.pullbackMapComparison
      (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
        (IsPullback.of_hasPullback c.g f).toCommSq.flip) :=
  MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
      (IsPullback.of_hasPullback c.g f).flip

attribute [local instance] siteBC_iso

private noncomputable abbrev testObject (W : U.Etale) : (pullback c.g f).Etale :=
  (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd c.g f)).obj W

private noncomputable def graphTestMap (W : U.Etale) :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale (sectionMap f c))).obj W ⟶
      testObject f c W :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) (W.hom ≫ sectionMap f c) (by simp [sectionMap, pullback.lift_snd]))
    (by simp) trivial

private noncomputable def graphTestMap' (W : U.Etale) :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale c.i)).obj W ⟶
      (MorphismProperty.Over.map ⊤
        (inferInstance : Etale (pullback.fst c.g f))).obj (testObject f c W) :=
  (MorphismProperty.Over.mapComp (Q := ⊤) (P := @Etale)
    (hf := inferInstance) (hg := inferInstance) c.i
      (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app W ≫
      (MorphismProperty.Over.map ⊤
        (inferInstance : Etale (pullback.fst c.g f))).map (graphTestMap f c W)

private theorem graphTestMap_geometry (W : U.Etale) :
    Scheme.Etale.graph f W ≫
      (MorphismProperty.Over.pullbackComp c.i c.g f c.comm).hom.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W) ≫
      (MorphismProperty.Over.pullback @Etale ⊤ c.i).map
        (inv ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W)) =
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ c.i inferInstance trivial).unit.app W ≫
        (MorphismProperty.Over.pullback @Etale ⊤ c.i).map (graphTestMap' f c W) := by
  rw [← cancel_mono ((MorphismProperty.Over.pullback @Etale ⊤ c.i).map
    ((MorphismProperty.Over.pullbackMapComparison
      (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W))]
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [graphTestMap', graphTestMap, testObject, Scheme.Etale.graph_left,
        MorphismProperty.Over.pullbackMapComparison_app_left]
    · simp [graphTestMap', graphTestMap, testObject, Scheme.Etale.graph_left,
        MorphismProperty.Over.pullbackMapComparison_app_left, sectionMap, pullback.lift_fst]
  · simp [graphTestMap', graphTestMap, testObject, Scheme.Etale.graph_left]

private theorem transfer_restriction
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (upperStar (ModuleCat.{u + 1} A) (sectionMap f c)).map
      ((transfer A f c).app M ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)) =
      (sectionIso A f c).hom.app M ≫
        inv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.i).counit.app M) ≫
        (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c)
          (pullback.fst c.g f) c.i
            (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app
            ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (sectionMap f c)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (sectionMap f c)).unit.naturality
      ((transfer A f c).app M ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g f)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M))
  exact hn.symm.trans (transfer_toLowerStar_postunit A f c M)

private theorem normalizedTransfer_restriction
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (localizationRestriction (ModuleCat.{u + 1} A) (sectionMap f c) inferInstance).map
        (normalizedTransfer A f c M) =
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
        (sectionMap f c) inferInstance).inv.app _ ≫
      (sectionIso A f c).hom.app M ≫
      inv ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A)
        c.i inferInstance).counit.app M) ≫
      (localizationRestrictionComp' (ModuleCat.{u + 1} A) (sectionMap f c)
        (pullback.fst c.g f) c.i
          (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M) := by
  have hn := (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
    (pullback.fst c.g f) inferInstance).hom.naturality
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)
  have hc := upperStarIsoLocalizationRestriction_comp (ModuleCat.{u + 1} A)
    (sectionMap f c) (pullback.fst c.g f) c.i
      (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm
    ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M)
  have he : (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
      c.i inferInstance).hom.app ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M) ≫
      (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A)
        c.i inferInstance).counit.app M =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.i).counit.app M :=
    Adjunction.leftAdjointUniq_hom_app_counit _ _ M
  rw [← cancel_epi ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
    (sectionMap f c) inferInstance).hom.app _)]
  rw [← NatTrans.naturality]
  simp only [normalizedTransfer, Functor.map_comp, Category.assoc]
  have hn' := congrArg
    ((upperStar (ModuleCat.{u + 1} A) (sectionMap f c)).map) hn
  simp only [Functor.map_comp] at hn'
  rw [← reassoc_of% hn']
  rw [← Functor.map_comp_assoc, transfer_restriction A f c M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← hc]
  have he' := congrArg (fun z =>
    inv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.i).counit.app M) ≫
      z ≫ inv ((localizationRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} A) c.i inferInstance).counit.app M)) he
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
    IsIso.inv_hom_id_assoc] at he'
  rw [reassoc_of% he']

private theorem restrictionBC_iso :
    IsIso (localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq.flip) :=
  isIso_localizationRestrictionBaseChangeMap_of_isPullback
    (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback c.g f).flip

attribute [local instance] restrictionBC_iso

private theorem restrictionBC_inv_app
    (N : Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etaleᵒᵖ) :
    (inv ((localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app N)).hom.app W =
      N.obj.map (inv ((MorphismProperty.Over.pullbackMapComparison
        (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W.unop)).op := by
  have hm := congrArg (fun z => z.hom.app W)
    (IsIso.inv_hom_id ((localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app N))
  let e := asIso ((MorphismProperty.Over.pullbackMapComparison
    (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W.unop)
  have hmap : ((localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app N).hom.app W =
      N.obj.map e.hom.op := rfl
  have hm' : (inv ((localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app N)).hom.app W ≫
        N.obj.map e.hom.op = 𝟙 _ := hm
  have hk := congrArg (fun z => z ≫ N.obj.map e.inv.op) hm'
  simp only [Category.assoc, ← N.obj.map_comp, ← op_comp,
    e.inv_hom_id, op_id, Category.id_comp] at hk
  erw [N.obj.map_id] at hk
  erw [Category.comp_id] at hk
  exact hk

attribute [local irreducible] upperStarLowerStarAdjunction

private theorem graph_unit
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.snd c.g f)).unit.app M).hom.app (op W) ≫
      (((upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).obj M).obj.map
        (graphTestMap f c W).op) ≫
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
        (sectionMap f c) inferInstance).inv.app _).hom.app (op W) ≫
      ((sectionIso A f c).hom.app M).hom.app (op W) = 𝟙 _ := by
  have h := upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} A)
    (sectionMap f c) (pullback.snd c.g f) M (𝟙 U)
      (pullback.lift_snd c.i (𝟙 U) (by simpa using c.comm.symm)).symm
  have hi := upperStarId_hom_app_unit_app (ModuleCat.{u + 1} A) U M
  have h' := congrArg (fun z => z ≫
    (lowerStar (ModuleCat.{u + 1} A) (𝟙 U)).map
      ((upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c)
        (pullback.snd c.g f) (𝟙 U)
          (pullback.lift_snd c.i (𝟙 U) (by simpa using c.comm.symm)).symm).inv.app M ≫
        (upperStarId (ModuleCat.{u + 1} A) U).hom.app M)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc] at h'
  rw [hi] at h'
  rw [← (lowerStarComp (ModuleCat.{u + 1} A) (sectionMap f c)
    (pullback.snd c.g f) (𝟙 U)
      (pullback.lift_snd c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.naturality] at h'
  have hsec : (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c)
      (pullback.snd c.g f) (𝟙 U)
        (pullback.lift_snd c.i (𝟙 U) (by simpa using c.comm.symm)).symm).inv.app M ≫
      (upperStarId (ModuleCat.{u + 1} A) U).hom.app M =
        (sectionIso A f c).hom.app M := by
    unfold sectionIso
    rfl
  rw [hsec] at h'
  have hh := congrArg (fun z => z.hom.app (op W)) h'
  simp only [Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, lowerStar_map_hom_app, lowerStarComp_hom_app_hom_app,
    Functor.comp_map] at hh
  let a : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (sectionMap f c)).obj
      (testObject f c W) :=
    (MorphismProperty.Over.pullbackId @Etale ⊤ U).inv.app W ≫
      (MorphismProperty.Over.pullbackComp (sectionMap f c) (pullback.snd c.g f)
        (𝟙 U) (pullback.lift_snd c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app W
  have ha : (MorphismProperty.Over.map ⊤
      (inferInstance : Etale (sectionMap f c))).map a ≫
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (sectionMap f c)
        inferInstance trivial).counit.app (testObject f c W) = graphTestMap f c W := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;> simp [a, graphTestMap, testObject]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A)
      (sectionMap f c) inferInstance)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (sectionMap f c))
    ((upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).obj M)
  have hu' := congrArg (fun z => z.hom.app (op (testObject f c W))) hu
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app] at hu'
  change _ ≫ ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
    (sectionMap f c) inferInstance).inv.app _).hom.app _ = _ at hu'
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app'] at hu'
  have hh' := congrArg (fun z => z ≫ M.obj.map
    ((MorphismProperty.Over.pullbackId @Etale ⊤ U).inv.app W).op) hh
  simp only [lowerStarId, GrothendieckTopology.lowerStarId,
    Functor.sheafPushforwardContinuousId'_inv_app_hom_app] at hh'
  simp only [Functor.id_obj, Functor.comp_obj, Category.assoc,
    ← Functor.map_comp, ← op_comp] at hh'
  simp only [Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id] at hh'
  erw [M.obj.map_id] at hh'
  change _ = _ ≫ _ ≫ ((sectionIso A f c).hom.app M).hom.app _ ≫ M.obj.map a.op
    at hh'
  erw [← ((sectionIso A f c).hom.app M).hom.naturality] at hh'
  rw [← hu'] at hh'
  simp only [Category.assoc] at hh'
  have hn := ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
    (sectionMap f c) inferInstance).inv.app
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).obj M)).hom.naturality a.op
  erw [← reassoc_of% hn] at hh'
  simp only [localizationRestriction_obj_obj_map, ← Functor.map_comp_assoc,
    ← op_comp, Quiver.Hom.unop_op, ha] at hh'
  exact hh'.symm

private theorem normalizedTransfer_graph
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.snd c.g f)).unit.app M).hom.app (op W) ≫
      (normalizedTransfer A f c M).hom.app (op (testObject f c W)) ≫
      M.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ c.i).map
        (inv ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W))).op ≫
      M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g f c.comm).hom.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)).op ≫
      M.obj.map (Scheme.Etale.graph f W).op = 𝟙 _ := by
  simp only [← Functor.map_comp, ← op_comp]
  simp only [Category.assoc] at ⊢
  rw [graphTestMap_geometry f c W, op_comp, Functor.map_comp]
  simp only [graphTestMap', Functor.map_comp, op_comp, Category.assoc]
  change _ ≫ (normalizedTransfer A f c M).hom.app _ ≫
    ((localizationRestriction (ModuleCat.{u + 1} A) (pullback.fst c.g f)
      inferInstance).obj ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M)).obj.map
        (graphTestMap f c W).op ≫
    ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M).obj.map
      ((MorphismProperty.Over.mapComp (Q := ⊤) (P := @Etale)
        (hf := inferInstance) (hg := inferInstance) c.i
        (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).hom.app W).op ≫
    M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ c.i
      inferInstance trivial).unit.app W).op = _
  rw [← (normalizedTransfer A f c M).hom.naturality_assoc]
  have hr := congrArg (fun z => z.hom.app (op W))
    (normalizedTransfer_restriction A f c M)
  simp only [localizationRestriction_map_hom_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, localizationRestrictionComp'_hom_app_hom_app] at hr
  rw [hr]
  simp only [Category.assoc]
  simp only [← Functor.map_comp_assoc, ← op_comp, Iso.hom_inv_id_app, op_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have he : ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A)
      c.i inferInstance).counit.app M).hom.app (op W) =
    M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ c.i
      inferInstance trivial).unit.app W).op := rfl
  have hi := congrArg (fun z => z.hom.app (op W))
    (IsIso.inv_hom_id ((localizationRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} A) c.i inferInstance).counit.app M))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hi
  rw [← he, hi]
  simp only [Category.comp_id]
  exact graph_unit A f c M W

private noncomputable def toTest (W : U.Etale) :
    (Scheme.Etale.graphTarget f W).left ⟶ (testObject f c W).left :=
  ((MorphismProperty.Over.pullbackComp c.i c.g f c.comm).hom.app
    ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)).left ≫
  ((MorphismProperty.Over.pullback @Etale ⊤ c.i).map
    (inv ((MorphismProperty.Over.pullbackMapComparison
      (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W))).left ≫
  pullback.fst ((testObject f c W).hom ≫ pullback.fst c.g f) c.i

private theorem toTest_open (W : U.Etale) : IsOpenImmersion (toTest f c W) := by
  unfold toTest
  infer_instance

attribute [local instance] toTest_open

attribute [local irreducible] toTest

private theorem toTest_fst (W : U.Etale) :
    toTest f c W ≫ pullback.fst W.hom (pullback.snd c.g f) =
      pullback.fst (W.hom ≫ f) f := by
  let b := (MorphismProperty.Over.pullbackMapComparison
    (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
    (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W
  have hb : (inv b).left ≫ pullback.fst W.hom (pullback.snd c.g f) =
      pullback.fst (W.hom ≫ f) c.g := by
    rw [← cancel_epi b.left]
    have hi : b.left ≫ (inv b).left = 𝟙 _ :=
      congrArg (fun z => z.left) (IsIso.hom_inv_id b)
    rw [← Category.assoc, hi, Category.id_comp]
    simp [b, MorphismProperty.Over.pullbackMapComparison_app_left]
  unfold toTest
  erw [MorphismProperty.Over.pullback_map_left]
  simp only [Category.assoc]
  erw [pullback.lift_fst_assoc]
  simp only [Category.assoc]
  erw [hb]
  simp only [MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
  erw [pullbackLeftPullbackSndIso_inv_fst (W.hom ≫ f) c.g c.i]
  erw [pullback.lift_fst, Category.comp_id]
  rfl

private theorem toTest_base (W : U.Etale) :
    toTest f c W ≫ (testObject f c W).hom ≫ pullback.fst c.g f =
      pullback.snd (W.hom ≫ f) f ≫ c.i := by
  unfold toTest
  simp only [Category.assoc]
  have hp : pullback.fst ((testObject f c W).hom ≫ pullback.fst c.g f) c.i ≫
      (testObject f c W).hom ≫ pullback.fst c.g f =
        pullback.snd ((testObject f c W).hom ≫ pullback.fst c.g f) c.i ≫ c.i :=
    pullback.condition
  erw [hp]
  simp only [← Category.assoc]
  have h := MorphismProperty.Over.w
    ((MorphismProperty.Over.pullbackComp c.i c.g f c.comm).hom.app
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W) ≫
      (MorphismProperty.Over.pullback @Etale ⊤ c.i).map
        (inv ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W)))
  exact congrArg (fun z => z ≫ c.i) h

private noncomputable def complementObject (W : U.Etale) : (pullback c.g f).Etale :=
  Scheme.Etale.mk ((Scheme.Etale.graphComplι f W).left ≫
    toTest f c W ≫ (testObject f c W).hom)

private noncomputable def complementMap (W : U.Etale) :
    complementObject f c W ⟶ testObject f c W :=
  MorphismProperty.Over.homMk ((Scheme.Etale.graphComplι f W).left ≫ toTest f c W)
    (by simp [complementObject]) trivial

private theorem complement_empty (W : U.Etale) :
    IsEmpty ((MorphismProperty.Over.pullback @Etale ⊤ (sectionMap f c)).obj
      (complementObject f c W)).left := by
  let B := complementObject f c W
  let e := pullback.fst B.hom (sectionMap f c)
  let d := pullback.snd B.hom (sectionMap f c)
  let k := (Scheme.Etale.graphComplι f W).left
  have h : e ≫ k ≫ toTest f c W ≫ (testObject f c W).hom =
      d ≫ sectionMap f c := pullback.condition
  have hv : e ≫ k ≫ pullback.snd (W.hom ≫ f) f = d := by
    apply (cancel_mono c.i).1
    have hv := congrArg (fun z => z ≫ pullback.fst c.g f) h
    simpa only [Category.assoc, toTest_base, sectionMap, pullback.lift_fst] using hv
  have hq : e ≫ k ≫ pullback.fst (W.hom ≫ f) f ≫ W.hom = d := by
    have hq := congrArg (fun z => z ≫ pullback.snd c.g f) h
    have hp : (testObject f c W).hom ≫ pullback.snd c.g f =
        pullback.fst W.hom (pullback.snd c.g f) ≫ W.hom :=
      pullback.condition.symm
    simp only [Category.assoc, sectionMap, pullback.lift_snd, Category.comp_id, hp,
      reassoc_of% (toTest_fst f c W)] at hq
    exact hq
  have he : e ≫ k = (e ≫ k ≫ pullback.fst (W.hom ≫ f) f) ≫
      (Scheme.Etale.graph f W).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [Scheme.Etale.graph_left_fst f W, Category.comp_id]
      rfl
    · simp only [Category.assoc]
      erw [Scheme.Etale.graph_left_snd f W]
      exact hv.trans hq.symm
  refine ⟨fun x => ?_⟩
  have hx := congrArg (fun z => z x) he
  have hd := (Scheme.Etale.isCompl_range_graph f W).disjoint
  exact Set.disjoint_left.mp hd
    ⟨(e ≫ k ≫ pullback.fst (W.hom ≫ f) f) x, hx.symm⟩ ⟨e x, rfl⟩

private noncomputable def complementLift (W : U.Etale) :
    Scheme.Etale.graphComplObj f W ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ c.i).obj
        ((MorphismProperty.Over.map ⊤
          (inferInstance : Etale (pullback.fst c.g f))).obj
            (complementObject f c W)) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 _) (Scheme.Etale.graphComplObj f W).hom (by
      change (Scheme.Etale.graphComplι f W).left ≫ toTest f c W ≫
        (testObject f c W).hom ≫ pullback.fst c.g f =
          (Scheme.Etale.graphComplι f W).left ≫
            pullback.snd (W.hom ≫ f) f ≫ c.i
      exact congrArg (fun z => (Scheme.Etale.graphComplι f W).left ≫ z)
        (toTest_base f c W)))
    (by simp) trivial

private theorem complement_geometry (W : U.Etale) :
    Scheme.Etale.graphComplι f W ≫
      (MorphismProperty.Over.pullbackComp c.i c.g f c.comm).hom.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W) ≫
      (MorphismProperty.Over.pullback @Etale ⊤ c.i).map
        (inv ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W)) =
      complementLift f c W ≫
        (MorphismProperty.Over.pullback @Etale ⊤ c.i).map
          ((MorphismProperty.Over.map ⊤
            (inferInstance : Etale (pullback.fst c.g f))).map
              (complementMap f c W)) := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono
    (pullback.fst ((testObject f c W).hom ≫ pullback.fst c.g f) c.i)).1
  simp [complementLift, complementMap, toTest, Category.assoc,
    MorphismProperty.Over.pullback_map_left]

private theorem normalizedTransfer_complement_zero
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale) :
    (normalizedTransfer A f c M).hom.app (op (complementObject f c W)) = 0 := by
  have hz := section_extension_zero A f c M (complementObject f c W)
    (complement_empty f c W)
  have hp : ((projection A f c).app M).hom.app
      (op (complementObject f c W)) = 0 := hz.eq_of_tgt _ _
  simp only [normalizedTransfer, transfer, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, hp, zero_comp]

private theorem normalizedTransfer_complement
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.snd c.g f)).unit.app M).hom.app (op W) ≫
      (normalizedTransfer A f c M).hom.app (op (testObject f c W)) ≫
      M.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ c.i).map
        (inv ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : Etale f) (inferInstance : Etale (pullback.fst c.g f))
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app W))).op ≫
      M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g f c.comm).hom.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)).op ≫
      M.obj.map (Scheme.Etale.graphComplι f W).op = 0 := by
  simp only [← Functor.map_comp, ← op_comp]
  rw [Category.assoc (Scheme.Etale.graphComplι f W),
    complement_geometry f c W, op_comp, Functor.map_comp]
  change _ ≫ (normalizedTransfer A f c M).hom.app _ ≫
    ((localizationRestriction (ModuleCat.{u + 1} A) (pullback.fst c.g f)
      inferInstance).obj ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M)).obj.map
        (complementMap f c W).op ≫ M.obj.map (complementLift f c W).op = _
  rw [← (normalizedTransfer A f c M).hom.naturality_assoc]
  rw [normalizedTransfer_complement_zero]
  simp

private theorem normalization_formula
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv M
        ((f)_*[ModuleCat.{u + 1} A].obj M)
      ((etaleCompactificationGraphMap A f c).app M ≫
        (compactificationSheafToDirectImage A c).app M) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd c.g f)).unit.app M ≫
        (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).map
          (normalizedTransfer A f c M) ≫
        inv ((localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g f).toCommSq.flip).app
          ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M)) ≫
        (localizationRestriction (ModuleCat.{u + 1} A) f inferInstance).map
          ((lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom.app M) := by
  have h := comparison_restriction_unit A f c M
  have h' := congrArg (fun z => z ≫
    (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).map
      ((localizationRestriction (ModuleCat.{u + 1} A) (pullback.fst c.g f)
        inferInstance).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)) ≫
    inv ((localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq.flip).app
        ((lowerStar (ModuleCat.{u + 1} A) c.i).obj M)) ≫
    (localizationRestriction (ModuleCat.{u + 1} A) f inferInstance).map
      ((lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom.app M)) h
  simp only [Category.assoc] at h'
  erw [← (localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback c.g f).toCommSq.flip).naturality_assoc] at h'
  simpa only [Adjunction.homEquiv_unit, compactificationSheafToDirectImage,
    NatTrans.comp_app, Functor.whiskerRight_app, normalizedTransfer, Functor.map_comp,
    Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc] using h'

end GraphNormalization

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transpose of the graph comparison is the graph extension unit.
Source: Stacks Project Tag 0F4L and SGA 4 XVII 6.2.11; the adjunction-transpose part
of the graph restriction calculation.
Proof: transpose the explicit graph map through the lower-shriek restriction adjunction;
then simplify the graph and complement restrictions using the clopen decomposition.
(auxiliary; not a blueprint node).
-/
theorem compactSupportGraphSheafComparison_normalization_transpose
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X)
    [Etale f] [IsSeparated f] (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv M
        ((f)_*[ModuleCat.{u + 1} A].obj M)
      ((etaleCompactificationGraphMap A f c).app M ≫
        (compactificationSheafToDirectImage A c).app M) =
      (lowerStarUnit (ModuleCat.{u + 1} A) f).app M := by
  rw [GraphNormalization.normalization_formula A f c M]
  apply Sheaf.hom_ext
  ext W : 2
  refine Scheme.Etale.graph_hom_ext f M ?_ ?_
  · simp only [lowerStarUnit_app_hom_app, Scheme.Etale.graphExtend_graph,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      GraphNormalization.restrictionBC_inv_app, localizationRestriction_map_hom_app,
      lowerStar_map_hom_app, lowerStarComp_hom_app_hom_app]
    erw [localizationRestriction_map_hom_app]
    erw [lowerStarComp_hom_app_hom_app]
    erw [lowerStar_map_hom_app]
    simp only [Category.assoc]

    exact GraphNormalization.normalizedTransfer_graph A f c M W.unop
  · simp only [lowerStarUnit_app_hom_app, Scheme.Etale.graphExtend_graphComplι,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      GraphNormalization.restrictionBC_inv_app, localizationRestriction_map_hom_app,
      lowerStar_map_hom_app, lowerStarComp_hom_app_hom_app]
    erw [localizationRestriction_map_hom_app]
    erw [lowerStarComp_hom_app_hom_app]
    erw [lowerStar_map_hom_app]
    simp only [Category.assoc]

    exact GraphNormalization.normalizedTransfer_complement A f c M W.unop

/-- The graph transpose extends each sheet section by zero in the compactification.
Source: Stacks Project Tag 0F4L, lemma-shriek-into-star-separated-etale;
SGA 4 XVII 6.2.11.
(auxiliary; not a blueprint node).

Proof:
1. Transpose both sides under the sum-extension/restriction adjunction. A section over
an etale test object is thereby tested on each lift of that object to U.
2. The inverse beta in the graph projection identifies that lift with its base change
in Z times_X U. The composition comparison preserves the same left-adjoint units.
3. The projection to the graph is identity on the graph and zero on its complement:
its map into the graph direct image is the adjoint of the section identity, and the
clopen comparison between extension and direct image is inverted.
4. Inclusion of extension by zero into direct image keeps the underlying section.
Both transposes are therefore the graph-extension unit defining
etaleLowerShriekToLowerStar. Injectivity of the adjunction bijection proves equality.
Concretely, apply the injective homEquiv of etaleLowerShriekRestrictionAdjunction,
then lowerStarUnit_app_hom_app. Scheme.Etale.graph_hom_ext reduces the resulting
section equation to its graph and complement restrictions. The target restrictions
are graphExtend_graph and graphExtend_graphComplι. For the constructed transpose,
the inverse-conjugate counit equation for beta, the counit equation for leftAdjointUniq,
and the triangle identity for the clopen projection give respectively identity and zero.
The argument is valid for the empty graph, where all relevant sections are zero. -/
theorem compactSupportGraphSheafComparison_normalization
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X)
    [Etale f] [IsSeparated f] (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleCompactificationGraphMap A f c).app M ≫
        (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M := by
  apply ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  rw [compactSupportGraphSheafComparison_normalization_transpose A f c M]
  rw [etaleLowerShriekToLowerStar]
  exact (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.Etale
