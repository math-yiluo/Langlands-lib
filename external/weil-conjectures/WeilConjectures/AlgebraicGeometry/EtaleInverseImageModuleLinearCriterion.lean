/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleUnitLinearLift
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleCounitLinearLift
/-! # Linearity under the etale abelian adjunction

Source: Stacks Project, Tag 03D3
(blueprint: lem-weil-pbc-inverse-image-module-linear-criterion). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The abelian adjunction preserves and reflects linearity for the transported action.
Source: Stacks Project, Tag 03D3, with the omitted converse supplied by the
naturality and triangle-identity calculation in the parent node, steps 2--5
(blueprint: lem-weil-pbc-inverse-image-module-linear-criterion).

Proof: the ring and abelian hom-equivalence hypotheses identify their underlying
units and counits with those of the set adjunction. On the action of G, naturality
of the set unit gives eta_G composed with mu_G equal to the direct image of the
transported action composed with eta_O times eta_G. Compatibility with each product
projection proves that eta_G is linear. For F, naturality of the set counit at mu_F
reduces counit linearity to equality of two maps into L(O) times F. On the scalar
projection this is the left triangle identity at O; on the module projection it is
counit naturality. Thus the counit is linear too. Direct image preserves linear
maps by sectionwise restriction of scalars along the ring unit, and LM preserves
linear maps by its functorial underlying comparison e and the action hypothesis.
The formulas beta = eta_G followed by R(alpha) and alpha = L(beta) followed by
epsilon_F prove both directions of linearity. For each linear abelian map, its
sectionwise scalar compatibility supplies a morphism
of sheaves of modules via `PresheafOfModules.homMk`. Conversely every such morphism
satisfies that scalar identity. These constructions give precisely the two
existential lift conditions in the statement. -/
theorem etaleInverseImageModuleLinearCriterion (U V : Scheme.{u}) (f : U ⟶ V)
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
    ∀ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
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
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L)
      (LM : SheafOfModules.{u + 1} OV ⥤ SheafOfModules.{u + 1} OR)
      (e : LM ⋙ FU ≅ FV ⋙ La),
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
            prod.map (er.inv.app O) iG.inv ≫ muU ≫ iG.hom) →
      (∀ (G : SheafOfModules.{u + 1} OV) (F : SheafOfModules.{u + 1} OR)
          (alpha : La.obj (FV.obj G) ⟶ FU.obj F),
        (∃ h : LM.obj G ⟶ F, FU.map h = e.hom.app G ≫ alpha) ↔
          ∃ k : G ⟶ RM.obj F, FV.map k = a.homEquiv (FV.obj G) (FU.obj F) alpha) := by
  intro L La a FaU FaV FrU FrV b aS Rr Lr ar er OR OV eta RM FV FU ea LM e H G F alpha
  obtain ⟨kG, hkG⟩ := etaleInverseImageModuleUnitLinearLift U V f O Lr ar er ea LM e H G
  obtain ⟨hF, hhF⟩ := etaleInverseImageModuleCounitLinearLift U V f O Lr ar er ea LM e H F
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨kG ≫ RM.map h, ?_⟩
    rw [FV.map_comp, hkG]
    change a.homEquiv _ _ (e.inv.app G) ≫ (Etale.lowerStar _ f).map (FU.map h) = _
    rw [← a.homEquiv_naturality_right, hh]
    simp
  · rintro ⟨k, hk⟩
    refine ⟨LM.map k ≫ hF, ?_⟩
    rw [FU.map_comp, hhF]
    change (LM ⋙ FU).map k ≫ e.hom.app (RM.obj F) ≫
      a.counit.app (FU.obj F) = _
    rw [← Category.assoc, e.hom.naturality k, Category.assoc]
    change e.hom.app G ≫ La.map (FV.map k) ≫ a.counit.app (FU.obj F) = _
    rw [hk]
    congr 1
    exact (a.homEquiv (FV.obj G) (FU.obj F)).symm_apply_apply alpha


end AlgebraicGeometry
