/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # EtaleModuleRingIsoAdjunction

Source: Stacks Project, Tags 03D3, 03D6, 03D7.
(blueprint: lem-weil-pbc-etale-module-ring-iso-adjunction). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a linearity criterion through an isomorphism of ring sheaves.
Source: Stacks Project, Tags 03D3 and 03D7, specialized to an invertible ring map.

Proof: let LM be L0 followed by restriction of scalars along c.inv. Restriction
along c.hom and c.inv are inverse equivalences: on sections their composite actions
are the original action, by the two inverse-ring equations. Their identity maps
on abelian groups give the comparison t. Define e by composing t with e0 after
forgetting. A map from LM(G) to F is RU-linear precisely when the same abelian map
from L0(G) to restriction of F along c.hom is Lr(RV)-linear. Apply hlin to this map.
Its adjunct is RV-linear for gamma, because the adjunct of c.hom is gamma (hc):
the hom-equivalence formula gives gamma = ar.unit.app RV followed by pushforward
of c.hom. Thus direct image followed by scalar restriction is exactly pushforward
along gamma. Restrict the abelian hom equivalence to these linear morphisms.
Faithfulness makes the lifts unique; naturality gives the module adjunction am.
The identity underlying t proves the comparison equation, and the restricted
hom equivalence gives the final displayed equation.
(blueprint: lem-weil-pbc-etale-module-ring-iso-adjunction). -/
theorem etaleModuleRingIsoAdjunction (U V : Scheme.{u}) (f : U ⟶ V)
    (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
      (ar : Lr ⊣ (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale))
      (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale)).obj RU) (c : Lr.obj RV ≅ RU)
    (hc :
      ar.homEquiv RV RU c.hom = gamma)
    (L0 : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
    (e0 : L0 ⋙ SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)) ≅ SheafOfModules.toSheaf
        ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
        ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f)
    (hlin : ∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)) (F : SheafOfModules.{u + 1}
        ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
          (alpha : (Etale.upperStar AddCommGrpCat.{u + 1} f).obj ((SheafOfModules.toSheaf
        ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G) ⟶
        (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV))).obj F),
        (∃ h : L0.obj G ⟶ F, (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV))).map h = e0.hom.app G
        ≫ alpha) ↔
          ∃ k : G ⟶ (SheafOfModules.pushforward
        (J := V.smallGrothendieckTopology @Etale)
        (K := U.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f)
        ((sheafCompose V.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (ar.unit.app RV))).obj F,
        (SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).map k =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
        ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G)
        ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV))).obj F) alpha) :
    ∃ (LM : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
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
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)).map h)) := by
  classical
  let CV := sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let CU := sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let FV := SheafOfModules.toSheaf.{u + 1} (CV.obj RV)
  let F0 := SheafOfModules.toSheaf.{u + 1} (CU.obj (Lr.obj RV))
  let FU := SheafOfModules.toSheaf.{u + 1} (CU.obj RU)
  let R0 := SheafOfModules.pushforward.{u + 1}
    (J := V.smallGrothendieckTopology @Etale) (K := U.smallGrothendieckTopology @Etale)
    (R := CU.obj (Lr.obj RV)) (S := CV.obj RV)
    (F := MorphismProperty.Over.pullback @Etale ⊤ f) (CV.map (ar.unit.app RV))
  let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  have forward (G) (F) (h : L0.obj G ⟶ F) :
      ∃ k : G ⟶ R0.obj F,
        FV.map k = a.homEquiv (FV.obj G) (F0.obj F) (e0.inv.app G ≫ F0.map h) := by
    apply (hlin G F _).mp
    exact ⟨h, by simp [F0, CU]⟩
  have backward (G) (F) (k : G ⟶ R0.obj F) :
      ∃ h : L0.obj G ⟶ F,
        F0.map h = e0.hom.app G ≫ (a.homEquiv (FV.obj G) (F0.obj F)).symm (FV.map k) := by
    apply (hlin G F _).mpr
    exact ⟨k, by simp [a, FV, F0, CV, CU]⟩
  let he (G) (F) : (L0.obj G ⟶ F) ≃ (G ⟶ R0.obj F) :=
    { toFun := fun h ↦ (forward G F h).choose
      invFun := fun k ↦ (backward G F k).choose
      left_inv := fun h ↦ by
        apply F0.map_injective
        rw [(backward G F _).choose_spec, (forward G F h).choose_spec]
        simp
      right_inv := fun k ↦ by
        apply FV.map_injective
        rw [(forward G F _).choose_spec, (backward G F k).choose_spec]
        simp }
  have he_spec (G) (F) (h : L0.obj G ⟶ F) :
      FV.map (he G F h) =
        a.homEquiv (FV.obj G) (F0.obj F) (e0.inv.app G ≫ F0.map h) :=
    (forward G F h).choose_spec
  have he_inv_spec (G) (F) (k : G ⟶ R0.obj F) :
      F0.map ((he G F).symm k) =
        e0.hom.app G ≫ (a.homEquiv (FV.obj G) (F0.obj F)).symm (FV.map k) :=
    (backward G F k).choose_spec
  let core : Adjunction.CoreHomEquiv L0 R0 :=
    { homEquiv := he
      homEquiv_naturality_left_symm := by
        intro G' G F g k
        apply F0.map_injective
        rw [he_inv_spec, F0.map_comp, he_inv_spec, FV.map_comp]
        rw [a.homEquiv_naturality_left_symm]
        have hn := e0.hom.naturality g
        dsimp at hn
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ (a.homEquiv (FV.obj G) (F0.obj F)).symm (FV.map k)) hn.symm
      homEquiv_naturality_right := by
        intro G F F' h g
        apply FV.map_injective
        rw [he_spec, FV.map_comp, he_spec, F0.map_comp]
        rw [← Category.assoc, a.homEquiv_naturality_right]
        rfl }
  let a0 := Adjunction.mkOfHomEquiv core
  have a0_spec (G) (F) (h : L0.obj G ⟶ F) :
      FV.map (a0.homEquiv G F h) =
        a.homEquiv (FV.obj G) (F0.obj F) (e0.inv.app G ≫ F0.map h) := by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    exact he_spec G F h
  let : (𝟭 U.Etale).IsContinuous
      (U.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale) :=
    Functor.isContinuous_id _
  let ci := CU.mapIso c
  let P := SheafOfModules.pushforward.{u + 1}
    (J := U.smallGrothendieckTopology @Etale) (K := U.smallGrothendieckTopology @Etale)
    (R := CU.obj (Lr.obj RV)) (S := CU.obj RU) (F := 𝟭 U.Etale) ci.inv
  let Q := SheafOfModules.pushforward.{u + 1}
    (J := U.smallGrothendieckTopology @Etale) (K := U.smallGrothendieckTopology @Etale)
    (R := CU.obj RU) (S := CU.obj (Lr.obj RV)) (F := 𝟭 U.Etale) ci.hom
  let ui : 𝟭 _ ≅ P ⋙ Q :=
    (SheafOfModules.pushforwardComp.{u + 1}
      (J := U.smallEtaleTopology) (K := U.smallEtaleTopology)
      (K' := U.smallEtaleTopology) (F := 𝟭 U.Etale) (G := 𝟭 U.Etale)
      (S := CU.obj (Lr.obj RV)) (R := CU.obj RU) (R' := CU.obj (Lr.obj RV))
      ci.hom ci.inv ≪≫
      SheafOfModules.pushforwardCongr (F := 𝟭 U.Etale) ci.hom_inv_id ≪≫
      SheafOfModules.pushforwardId _).symm
  let co : Q ⋙ P ≅ 𝟭 _ :=
    SheafOfModules.pushforwardComp.{u + 1}
      (J := U.smallEtaleTopology) (K := U.smallEtaleTopology)
      (K' := U.smallEtaleTopology) (F := 𝟭 U.Etale) (G := 𝟭 U.Etale)
      (S := CU.obj RU) (R := CU.obj (Lr.obj RV)) (R' := CU.obj RU)
      ci.inv ci.hom ≪≫
      SheafOfModules.pushforwardCongr (F := 𝟭 U.Etale) ci.inv_hom_id ≪≫
      SheafOfModules.pushforwardId _
  let E : SheafOfModules.{u + 1} (CU.obj (Lr.obj RV)) ≌
      SheafOfModules.{u + 1} (CU.obj RU) :=
    { functor := P
      inverse := Q
      unitIso := ui
      counitIso := co
      functor_unitIso_comp := by
        intro M
        ext X x
        rfl }
  let LM := L0 ⋙ E.functor
  let t : LM ⋙ E.inverse ≅ L0 :=
    (Functor.associator L0 E.functor E.inverse) ≪≫
      L0.isoWhiskerLeft E.unitIso.symm ≪≫ L0.rightUnitor
  let ef : E.functor ⋙ FU ≅ F0 := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let e : LM ⋙ FU ≅ FV ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f :=
    Functor.associator _ _ _ ≪≫ L0.isoWhiskerLeft ef ≪≫ e0
  let : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      V.smallEtaleTopology U.smallEtaleTopology := by
    change (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    infer_instance
  let r : E.inverse ⋙ R0 ≅ SheafOfModules.pushforward.{u + 1}
      (J := V.smallGrothendieckTopology @Etale) (K := U.smallGrothendieckTopology @Etale)
      (F := MorphismProperty.Over.pullback @Etale ⊤ f) (CV.map gamma) :=
    SheafOfModules.pushforwardComp.{u + 1}
      (J := V.smallEtaleTopology) (K := U.smallEtaleTopology)
      (K' := U.smallEtaleTopology)
      (F := MorphismProperty.Over.pullback @Etale ⊤ f) (G := 𝟭 U.Etale)
      (S := CV.obj RV) (R := CU.obj (Lr.obj RV)) (R' := CU.obj RU)
      (CV.map (ar.unit.app RV)) ci.hom ≪≫
      SheafOfModules.pushforwardCongr
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) (by
        have hh := hc
        rw [Adjunction.homEquiv_unit] at hh
        exact congrArg CV.map hh)
  let am := (a0.comp E.toAdjunction).ofNatIsoRight r
  refine ⟨LM, e, t, am, ?_, ?_⟩
  · intro G
    ext X x
    rfl
  · intro G F h
    change FV.map (am.homEquiv G F h) = _
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change FV.map (a0.homEquiv G (E.inverse.obj F)
      (E.toAdjunction.homEquiv (L0.obj G) F h) ≫ r.hom.app F) = _
    have hr (k : G ⟶ R0.obj (E.inverse.obj F)) :
        FV.map (k ≫ r.hom.app F) = FV.map k := by
      ext X x
      rfl
    rw [hr, a0_spec]
    change a.homEquiv (FV.obj G) (FU.obj F) _ = a.homEquiv (FV.obj G) (FU.obj F) _
    congr 1

end AlgebraicGeometry
