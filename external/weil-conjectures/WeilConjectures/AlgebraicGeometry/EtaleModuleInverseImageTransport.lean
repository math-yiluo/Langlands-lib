/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import WeilConjectures.AlgebraicGeometry.EtaleModuleRingIsoAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleModuleRingIsoTensor

/-!
# Transport of the etale module inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2, 03D3, 03D6, 03D7, 04JC;
Sites and Sheaves, Example 0H7J
(blueprint: lem-weil-pbc-etale-module-inverse-image-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

private theorem adjunctionForgetUnitCounit
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (L : C ⥤ D) (R : D ⥤ C) (La : A ⥤ B) (Ra : B ⥤ A)
    (P : C ⥤ A) (Q : D ⥤ B) (am : L ⊣ R) (a : La ⊣ Ra)
    (e : L ⋙ Q ≅ P ⋙ La) (d : R ⋙ P ≅ Q ⋙ Ra)
    (hm : ∀ (G : C) (F : D) (h : L.obj G ⟶ F),
      P.map (am.homEquiv G F h) ≫ d.hom.app F =
        a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h)) :
    (∀ G : C, P.map (am.unit.app G) ≫ d.hom.app (L.obj G) =
      a.unit.app (P.obj G) ≫ Ra.map (e.inv.app G)) ∧
    (∀ F : D, Q.map (am.counit.app F) =
      e.hom.app (R.obj F) ≫ La.map (d.hom.app F) ≫ a.counit.app (Q.obj F)) := by
  constructor
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

/-- Forgetting module structure transports the unit and counit to the abelian adjunction. -/
private theorem etaleModuleAdjunction_unit_counit
    (U V : Scheme.{u}) (f : U ⟶ V)
    (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale)
        (U.smallGrothendieckTopology @Etale)).obj RU) :
  let FV := SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
  let FU := SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
  let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let RM := SheafOfModules.pushforward.{u + 1}
    (S := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
    (R := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
    (J := V.smallGrothendieckTopology @Etale) (K := U.smallGrothendieckTopology @Etale)
    (F := MorphismProperty.Over.pullback @Etale ⊤ f)
    ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      gamma)
  ∀ (LM : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV) ⥤
      SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
    (am : LM ⊣ RM) (e : LM ⋙ FU ≅ FV ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f),
    (∀ G F h, FV.map (am.homEquiv G F h) =
      a.homEquiv (FV.obj G) (FU.obj F) (e.inv.app G ≫ FU.map h)) →
    (∀ G, FV.map (am.unit.app G) =
      a.unit.app (FV.obj G) ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (e.inv.app G)) ∧
    (∀ F, FU.map (am.counit.app F) = e.hom.app (RM.obj F) ≫ a.counit.app (FU.obj F)) := by
  intro FV FU a RM LM am e hm
  let d : RM ⋙ FV ≅ FU ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} f := Iso.refl _
  have huc := adjunctionForgetUnitCounit LM RM
    (Etale.upperStar AddCommGrpCat.{u + 1} f)
    (Etale.lowerStar AddCommGrpCat.{u + 1} f) FV FU am a e d
    (fun G F h ↦ (Category.comp_id _).symm.trans (hm G F h))
  constructor
  · intro G
    exact (Category.comp_id _).symm.trans (huc.1 G)
  · intro F
    have he : e.hom.app (RM.obj F) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} f).map (d.hom.app F) ≫
          a.counit.app (FU.obj F) = e.hom.app (RM.obj F) ≫ a.counit.app (FU.obj F) :=
      (congrArg (fun k ↦ e.hom.app (RM.obj F) ≫ k ≫ a.counit.app (FU.obj F))
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).map_id _)).trans
          (congrArg (fun k ↦ e.hom.app (RM.obj F) ≫ k) (Category.id_comp _))
    exact (huc.2 F).trans he

/-- Transport the module inverse image and its adjunction along a ring comparison.
Source: Stacks Project, Modules on Sites, Lemmas 03D2, 03D3, 03D7 and Definition 03D6.
(blueprint: lem-weil-pbc-etale-module-inverse-image-transport).

Proof: Use the module lift and adjunction of `etaleInverseImageModuleAdjunction`
for RV. Identify its ring lift with the supplied Lr by uniqueness of left
adjoints, using the hom-equivalence compatibility to identify their underlying
set comparisons. Transport the module action across this identification to
obtain L0 and e0. Applying the set pullback to the original action gives the
required action equation. The prescribed sectionwise scalar multiplication
uniquely determines muU, since morphisms of sheaves are determined by sections.
Restrict scalars along c.inv to obtain LM, the comparison t and e. The inverse
restriction along c.hom gives an equivalence. Compose this equivalence with
the module adjunction: its right adjoint is pushforward along gamma because
      ar.homEquiv c.hom = gamma. Under forgetting, the hom equivalence, unit and
counit are those of the abelian adjunction, with the displayed comparison e.
For the tensor comparison, sectionwise send a tensor m to c.inv(a) times m;
the inverse sends m to 1 tensor m. The balancing relation and the inverse-ring
identities prove these maps are inverse linear maps. They commute with
restriction and module morphisms, and sheafification gives d and its formulas.
No exactness is asserted here. -/
theorem etaleModuleInverseImageTransport (U V : Scheme.{u}) (f : U ⟶ V)
    (R : CommRingCat.{u + 1})
    (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (etaV : ((Functor.const V.Etaleᵒᵖ).obj R) ⟶ RV.obj)
    (etaU : ((Functor.const U.Etaleᵒᵖ).obj R) ⟶ RU.obj)
    (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
      (ar : Lr ⊣ (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale))
      (er : Lr ⋙ sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology ≅ sheafForget (D :=
        CommRingCat.{u + 1}) V.smallEtaleTopology ⋙ Scheme.etaleSetPullback f)
      (ea : Etale.upperStar AddCommGrpCat.{u + 1} f ⋙ sheafForget (D := AddCommGrpCat.{u + 1})
        U.smallEtaleTopology ≅ sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology ⋙
        Scheme.etaleSetPullback f)
      (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale)).obj RU) (c : Lr.obj RV ≅ RU)
    (hc :
      ar.homEquiv RV RU c.hom = gamma)
    (hconst :
      (∀ (W : V.Etaleᵒᵖ) (r : R),
      gamma.hom.app W ((etaV).app W r) =
        (etaU).app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r))
    (hr :
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
      (sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).map (ar.homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          CommRingCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := CommRingCat.{u +
          1}) U.smallEtaleTopology).obj F)
          (er.inv.app G ≫ (sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).map h)))
    (ha :
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : (Etale.upperStar
        AddCommGrpCat.{u + 1} f).obj G ⟶ F),
      (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := AddCommGrpCat.{u
          + 1}) U.smallEtaleTopology).obj F)
          (ea.inv.app G ≫ (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).map h)))
    :
    ∃ (L0 : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
      (LM : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
      (e0 : L0 ⋙ SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)) ≅ SheafOfModules.toSheaf
        ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
        ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f)
      (e : LM ⋙ SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u
        + 1} RingCat.{u + 1})).obj RU) ≅ SheafOfModules.toSheaf ((sheafCompose
        V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV) ⋙
        Etale.upperStar AddCommGrpCat.{u + 1} f)
      (t : LM ⋙ SheafOfModules.pushforward (F := 𝟭 U.Etale) ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom ≅ L0)
      (am : LM ⊣ SheafOfModules.pushforward (J := V.smallGrothendieckTopology @Etale) (K :=
        U.smallGrothendieckTopology @Etale) (F := MorphismProperty.Over.pullback @Etale ⊤ f)
        ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        gamma)),
    (∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RV),
      (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj (Lr.obj RV))).map (t.hom.app G) ≫ e0.hom.app G = e.hom.app G) ∧
    (∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RV),
      ∃ (muV : ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
        ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RV)).obj G)) ⟶
          (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RV)).obj G)),
      (∀ (W : V.Etaleᵒᵖ)
        (x : ((((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
          ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
          ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
          1} RingCat.{u + 1})).obj RV)).obj G))).obj.obj W)),
        HEq (muV.hom.app W x)
          (@SMul.smul (((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u
            + 1})).obj RV).obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
          ((prod.fst : ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
            ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RV)).obj G)) ⟶ (sheafForget (D := CommRingCat.{u + 1})
            V.smallEtaleTopology).obj RV).hom.app W x : ((sheafCompose V.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV).obj.obj W)
            ((prod.snd : ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
              ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
              ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u
              + 1} RingCat.{u + 1})).obj RV)).obj G)) ⟶ (sheafForget (D := AddCommGrpCat.{u + 1})
              V.smallEtaleTopology).obj ((SheafOfModules.toSheaf ((sheafCompose
              V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj
              G)).hom.app W x : G.val.obj W))) ∧
      ∃! (muU : ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj RV)) ⨯
          ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))) ⟶
          (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))),
      (∀ (W : U.Etaleᵒᵖ)
        (x : ((((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj RV)) ⨯
          ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G)))).obj.obj W)),
        HEq (muU.hom.app W x)
          (@SMul.smul (((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u
            + 1})).obj (Lr.obj RV)).obj.obj W) ((L0.obj G).val.obj W) ((L0.obj G).val.obj
            W).isModule.toSMul
          ((prod.fst : ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj
            RV)) ⨯ ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))) ⟶ (sheafForget (D :=
            CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj RV)).hom.app W x :
            ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (Lr.obj RV)).obj.obj W)
            ((prod.snd : ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj
              (Lr.obj RV)) ⨯ ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
              ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u
              + 1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))) ⟶ (sheafForget (D :=
              AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj ((SheafOfModules.toSheaf
              ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u +
              1})).obj (Lr.obj RV))).obj (L0.obj G))).hom.app W x : (L0.obj G).val.obj W))) ∧
      (Scheme.etaleSetPullback f).map muV =
        prodComparison (Scheme.etaleSetPullback f) ((sheafForget (D := CommRingCat.{u + 1})
          V.smallEtaleTopology).obj RV)
          ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RV)).obj G)) ≫
        prod.map (er.inv.app RV)
          (((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).mapIso (e0.app G) ≪≫
            ea.app ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G)).inv) ≫
        muU ≫ ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).mapIso (e0.app G) ≪≫
          ea.app ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G)).hom) ∧
    (∃ (d : ∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RV),
        SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom (L0.obj
          G) ≅ LM.obj G),
      (∀ (G H : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u
        + 1} RingCat.{u + 1})).obj RV)) (h : G ⟶ H),
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom
          (L0.obj G) (L0.map h) ≫ (d H).hom =
          (d G).hom ≫ LM.map h) ∧
      (∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV)) (W : U.Etaleᵒᵖ)
        (a : RU.obj.obj W) (m : (L0.obj G).val.obj W),
        (d G).hom.val.app W
          ((toSheafify U.smallEtaleTopology
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (J := U.smallEtaleTopology)
              c.hom (L0.obj G)).presheaf).app W
              (a ⊗ₜ[(Lr.obj RV).obj.obj W, (c.hom.hom.app W).hom] m)) =
          (t.inv.app G).val.app W ((c.inv.hom.app W a) • m))) ∧
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV)) (F : SheafOfModules.{u + 1} ((sheafCompose
      U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
      (h : LM.obj G ⟶ F),
      (SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RV)).map (am.homEquiv G F h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
          1} RingCat.{u + 1})).obj RV)).obj G)
          ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RU)).obj F)
          (e.inv.app G ≫ (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)).map h)) ∧
    (∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RV),
      (SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RV)).map (am.unit.app G) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
          1} RingCat.{u + 1})).obj RV)).obj G) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (e.inv.app G)) ∧
    (∀ F : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RU),
      (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RU)).map (am.counit.app F) =
        e.hom.app ((SheafOfModules.pushforward (J := V.smallGrothendieckTopology @Etale) (K :=
          U.smallGrothendieckTopology @Etale) (F := MorphismProperty.Over.pullback @Etale ⊤ f)
          ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          gamma)).obj F) ≫
          (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RU)).obj F)) := by
  have _ := hconst
  obtain ⟨L0, e0, hact⟩ := etaleInverseImageModuleConstruction U V f RV
    Lr ar er ea ⟨hr, ha⟩
  have hlin := etaleInverseImageModuleLinearCriterion U V f RV
    Lr ar er ea L0 e0 ⟨hr, ha, hact⟩
  obtain ⟨LM, e, t, am, ht, hm⟩ := etaleModuleRingIsoAdjunction U V f
    RV RU Lr ar gamma c hc L0 e0 hlin
  have huc := etaleModuleAdjunction_unit_counit U V f RV RU gamma LM am e hm
  have hd := etaleModuleRingIsoTensor U V f RV RU Lr c L0 LM t
  refine ⟨L0, LM, e0, e, t, am, ht, ?_, hd, hm, ?_, ?_⟩
  · intro G
    obtain ⟨muV, muU, hv, hu, hmu⟩ := hact G
    refine ⟨muV, ?_, muU, ⟨?_, hmu⟩, ?_⟩
    · intro W x
      exact heq_of_eq (hv W x)
    · intro W x
      exact heq_of_eq (hu W x)
    · intro nu hnu
      ext W x
      exact (eq_of_heq (hnu.1 W x)).trans (hu W x).symm
  · exact huc.1
  · exact huc.2

end AlgebraicGeometry
