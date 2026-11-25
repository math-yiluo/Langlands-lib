/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Inverse image of modules on small étale sites

Source: Stacks Project, Modules on Sites, Tags 03D1, 03D2 and 03D3
(blueprint: situation-conventions).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restrict a hom equivalence to morphisms seen by faithful forgetful functors.
Source: Stacks Project, Tag 03D3, restriction and naturality step;
Mathlib `Adjunction.mkOfHomEquiv` and its unit/counit formulas
(blueprint: situation-conventions). -/
private theorem adjunctionOfLinearLifts
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (L : C ⥤ D) (R : D ⥤ C) (La : A ⥤ B) (Ra : B ⥤ A)
    (P : C ⥤ A) (Q : D ⥤ B) [P.Faithful] [Q.Faithful]
    (a : La ⊣ Ra) (e : L ⋙ Q ≅ P ⋙ La) (d : R ⋙ P ≅ Q ⋙ Ra)
    (hl : ∀ (G : C) (F : D) (alpha : La.obj (P.obj G) ⟶ Q.obj F),
      (∃ h : L.obj G ⟶ F, Q.map h = e.hom.app G ≫ alpha) ↔
        ∃ k : G ⟶ R.obj F, P.map k ≫ d.hom.app F = a.homEquiv _ _ alpha) :
    ∃ am : L ⊣ R,
      (∀ (G : C) (F : D) (h : L.obj G ⟶ F),
        P.map (am.homEquiv G F h) ≫ d.hom.app F =
          a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h)) ∧
      (∀ G : C, P.map (am.unit.app G) ≫ d.hom.app (L.obj G) =
        a.unit.app (P.obj G) ≫ Ra.map (e.inv.app G)) ∧
      (∀ F : D, Q.map (am.counit.app F) =
        e.hom.app (R.obj F) ≫ La.map (d.hom.app F) ≫ a.counit.app (Q.obj F)) := by
  classical
  let forward (G : C) (F : D) (h : L.obj G ⟶ F) : G ⟶ R.obj F :=
    Classical.choose ((hl G F (e.inv.app G ≫ Q.map h)).mp ⟨h, by simp⟩)
  have hf (G : C) (F : D) (h : L.obj G ⟶ F) :
      P.map (forward G F h) ≫ d.hom.app F =
        a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h) :=
    Classical.choose_spec ((hl G F (e.inv.app G ≫ Q.map h)).mp ⟨h, by simp⟩)
  have hi (G : C) (F : D) : Function.Injective (forward G F) := by
    intro h k hhk
    apply Q.map_injective
    have hh := congrArg (fun t ↦ P.map t ≫ d.hom.app F) hhk
    rw [hf, hf] at hh
    have hh' := (a.homEquiv _ _).injective hh
    simpa using congrArg (fun t ↦ e.hom.app G ≫ t) hh'
  have hs (G : C) (F : D) : Function.Surjective (forward G F) := by
    intro k
    obtain ⟨h, hh⟩ := (hl G F ((a.homEquiv _ _).symm
      (P.map k ≫ d.hom.app F))).mpr ⟨k, by simp⟩
    refine ⟨h, P.map_injective ((cancel_mono (d.hom.app F)).mp ?_)⟩
    rw [hf, hh]
    simp
  let E (G : C) (F : D) : (L.obj G ⟶ F) ≃ (G ⟶ R.obj F) :=
    Equiv.ofBijective (forward G F) ⟨hi G F, hs G F⟩
  have hE (G : C) (F : D) (h : L.obj G ⟶ F) :
      P.map (E G F h) ≫ d.hom.app F =
        a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h) := hf G F h
  have hleft {G' G : C} {F : D} (g : G' ⟶ G) (h : L.obj G ⟶ F) :
      E G' F (L.map g ≫ h) = g ≫ E G F h := by
    apply P.map_injective
    apply (cancel_mono (d.hom.app F)).mp
    rw [hE, P.map_comp, Category.assoc, hE, Q.map_comp]
    have he : La.map (P.map g) ≫ e.inv.app G = e.inv.app G' ≫ Q.map (L.map g) :=
      e.inv.naturality g
    rw [← Category.assoc, ← he, Category.assoc]
    exact a.homEquiv_naturality_left (P.map g) (e.inv.app G ≫ Q.map h)
  let core : Adjunction.CoreHomEquiv L R :=
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro G' G F g k
        apply (E G' F).injective
        rw [Equiv.apply_symm_apply, hleft, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro G F F' h k
        apply P.map_injective
        apply (cancel_mono (d.hom.app F')).mp
        have hd : P.map (R.map k) ≫ d.hom.app F' =
            d.hom.app F ≫ Ra.map (Q.map k) := d.hom.naturality k
        rw [hE, P.map_comp, Category.assoc, hd,
          ← Category.assoc, hE, Q.map_comp]
        simpa only [Category.assoc] using
          a.homEquiv_naturality_right (e.inv.app G ≫ Q.map h) (Q.map k) }
  let am := Adjunction.mkOfHomEquiv core
  have hm (G : C) (F : D) (h : L.obj G ⟶ F) :
      P.map (am.homEquiv G F h) ≫ d.hom.app F =
        a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h) := by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    exact hE G F h
  refine ⟨am, hm, ?_, ?_⟩
  · intro G
    simpa [Adjunction.homEquiv_id, Adjunction.homEquiv_unit] using hm G (L.obj G) (𝟙 _)
  · intro F
    have h := hm (R.obj F) F (am.counit.app F)
    have hc : am.homEquiv (R.obj F) F (am.counit.app F) = 𝟙 _ := by
      rw [← am.homEquiv_symm_id F, Equiv.apply_symm_apply]
    rw [hc, P.map_id, Category.id_comp] at h
    have h' := congrArg (fun t ↦ (a.homEquiv (P.obj (R.obj F)) (Q.obj F)).symm t) h
    simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h'
    simpa using congrArg (fun t ↦ e.hom.app (R.obj F) ≫ t) h'.symm


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse image transports the scalar action and the abelian adjunction restricts to modules.
Source: Stacks Project, Tags 03D1--03D3
(blueprint: situation-conventions).

Proof:
1. By situation-conventions and
   situation-conventions, inverse image preserves products and
   transports the ring and group operations. Apply it to the module axioms to obtain
   the displayed action. Direct image is sectionwise, with restriction of scalars along
   the ring unit (03D1, 03D2); both constructions preserve linear maps.
2. Naturality of the set unit at the scalar action, together with its compatibility with
   product projections, proves that the abelian unit is linear (the square in 03D3).
3. Naturality of the counit at the scalar action proves that it is linear: on the first
   product projection use the triangle identity, and on the second use counit naturality.
   This supplies the implication omitted in 03D3.
4. By situation-conventions, the adjoint of alpha is R(alpha) after the
   unit, and alpha is L(beta) followed by the counit. Steps 1--3 prove both implications.
5. Restrict the abelian hom equivalence to the subsets of linear maps. Its naturality
   gives the module adjunction; its unit and counit are the linear maps of steps 2--3.
   The module category is situation-conventions. -/
theorem etaleInverseImageModuleAdjunction (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}) :
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let aS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
        Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
    let OR := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
    let OV := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
    let eta := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (ar.unit.app O)
    let RM := SheafOfModules.pushforward.{u + 1}
      (J := V.smallGrothendieckTopology @Etale)
      (K := U.smallGrothendieckTopology @Etale) (F := b) eta
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    let FU := SheafOfModules.toSheaf.{u + 1} OR
    ∃ (ea : La ⋙ FaU ≅ FaV ⋙ L)
      (LM : SheafOfModules.{u + 1} OV ⥤ SheafOfModules.{u + 1} OR)
      (e : LM ⋙ FU ≅ FV ⋙ La) (am : LM ⊣ RM),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) ∧
      (∀ G : SheafOfModules.{u + 1} OV,
        let iG := (FaU.mapIso (e.app G)) ≪≫ ea.app (FV.obj G)
        ∃ (muV : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶ FaV.obj (FV.obj G))
          (muU : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G))) ⟶
            FaU.obj (FU.obj (LM.obj G))),
          (∀ (W : V.Etaleᵒᵖ)
              (x : ((FrV.obj O) ⨯ (FaV.obj (FV.obj G))).obj.obj W),
            muV.hom.app W x =
              @SMul.smul (OV.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
              ((prod.fst : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FrV.obj O).hom.app W x : OV.obj.obj W)
              ((prod.snd : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FaV.obj (FV.obj G)).hom.app W x : G.val.obj W)) ∧
          (∀ (W : U.Etaleᵒᵖ)
              (x : ((FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G)))).obj.obj W),
            muU.hom.app W x =
              @SMul.smul (OR.obj.obj W) ((LM.obj G).val.obj W)
                ((LM.obj G).val.obj W).isModule.toSMul
              ((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G))) ⟶
                FrU.obj (Lr.obj O)).hom.app W x : OR.obj.obj W)
              ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G))) ⟶
                FaU.obj (FU.obj (LM.obj G))).hom.app W x : (LM.obj G).val.obj W)) ∧
          L.map muV = prodComparison L (FrV.obj O) (FaV.obj (FV.obj G)) ≫
            prod.map (er.inv.app O) iG.inv ≫ muU ≫ iG.hom) ∧
      (∀ (G : SheafOfModules.{u + 1} OV) (F : SheafOfModules.{u + 1} OR)
          (alpha : La.obj (FV.obj G) ⟶ FU.obj F),
        (∃ h : LM.obj G ⟶ F, FU.map h = e.hom.app G ≫ alpha) ↔
          ∃ k : G ⟶ RM.obj F, FV.map k = a.homEquiv (FV.obj G) (FU.obj F) alpha) ∧
      (∀ (G : SheafOfModules.{u + 1} OV) (F : SheafOfModules.{u + 1} OR)
          (h : LM.obj G ⟶ F),
        FV.map (am.homEquiv G F h) =
          a.homEquiv (FV.obj G) (FU.obj F) (e.inv.app G ≫ FU.map h)) ∧
      (∀ G : SheafOfModules.{u + 1} OV,
        FV.map (am.unit.app G) =
          a.unit.app (FV.obj G) ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
            (e.inv.app G)) ∧
      (∀ F : SheafOfModules.{u + 1} OR,
        FU.map (am.counit.app F) = e.hom.app (RM.obj F) ≫ a.counit.app (FU.obj F)) := by
  rcases etaleInverseImageAlgebraicStructures U V f with
    ⟨-, ea, da, Lr, ar, er, dr, hda, hdr, ha₀, -, hr₀, -, -, -⟩
  have hda' (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      da.hom.app F = 𝟙 _ := by
    ext W x
    exact hda F W x
  have hdr' (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) :
      dr.hom.app F = 𝟙 _ := by
    ext W x
    exact hdr F W x
  have ha := fun G F h ↦ ha₀ G F h
  have hr := fun G F h ↦ hr₀ G F h
  simp only [hda'] at ha
  simp only [hdr'] at hr
  obtain ⟨LM, e, hact⟩ := etaleInverseImageModuleConstruction U V f O
    Lr ar er ea ⟨hr, ha⟩
  let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let OR := (sheafCompose U.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
  let OV := (sheafCompose V.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let eta := (sheafCompose V.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (ar.unit.app O)
  let RM := SheafOfModules.pushforward.{u + 1}
    (J := V.smallGrothendieckTopology @Etale)
    (K := U.smallGrothendieckTopology @Etale)
    (F := MorphismProperty.Over.pullback @Etale ⊤ f) (S := OV) (R := OR) eta
  let FV := SheafOfModules.toSheaf.{u + 1} OV
  let FU := SheafOfModules.toSheaf.{u + 1} OR
  have hlin := etaleInverseImageModuleLinearCriterion U V f O
    Lr ar er ea LM e ⟨hr, ha, hact⟩
  let d : RM ⋙ FV ≅ FU ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} f := Iso.refl _
  obtain ⟨am, hm, hu, hc⟩ := adjunctionOfLinearLifts LM RM
    (Etale.upperStar AddCommGrpCat.{u + 1} f)
    (Etale.lowerStar AddCommGrpCat.{u + 1} f) FV FU a e d
    (fun G F alpha ↦ by
      constructor
      · intro hh
        obtain ⟨k, hk⟩ := (hlin G F alpha).mp hh
        exact ⟨k, (Category.comp_id _).trans hk⟩
      · rintro ⟨k, hk⟩
        exact (hlin G F alpha).mpr ⟨k, (Category.comp_id _).symm.trans hk⟩)
  refine ⟨Lr, ar, er, ea, LM, e, am, hr, ha, hact, hlin, ?_, ?_, ?_⟩
  · intro G F h
    exact (Category.comp_id _).symm.trans (hm G F h)
  · intro G
    exact (Category.comp_id _).symm.trans (hu G)
  · intro F
    have he : e.hom.app (RM.obj F) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} f).map (d.hom.app F) ≫
          a.counit.app (FU.obj F) = e.hom.app (RM.obj F) ≫ a.counit.app (FU.obj F) :=
      (congrArg (fun t ↦ e.hom.app (RM.obj F) ≫ t ≫ a.counit.app (FU.obj F))
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).map_id _)).trans
          (congrArg (fun t ↦ e.hom.app (RM.obj F) ≫ t) (Category.id_comp _))
    exact (hc F).trans he

end AlgebraicGeometry
