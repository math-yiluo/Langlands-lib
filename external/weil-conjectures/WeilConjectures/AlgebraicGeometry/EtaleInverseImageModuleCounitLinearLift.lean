/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
/-! # The transported abelian counit lifts to a module map

Source: Stacks Project, Tag 03D3
(blueprint: lem-weil-pbc-inverse-image-module-counit-linear-lift). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem counit_action.{uC, uD} {C : Type uC} [Category C] {D : Type uD} [Category D]
    [HasBinaryProducts C] [HasBinaryProducts D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [PreservesLimitsOfShape (Discrete WalkingPair) L]
    (X : C) (A B Y : D) (er : A ≅ L.obj X) (i : B ≅ L.obj (R.obj Y))
    (muV : X ⨯ R.obj Y ⟶ R.obj Y) (muB : A ⨯ B ⟶ B) (muY : A ⨯ Y ⟶ Y)
    (t : X ⨯ R.obj Y ⟶ R.obj (A ⨯ Y))
    (htf : t ≫ R.map prod.fst = prod.fst ≫ a.unit.app X ≫ R.map er.inv)
    (hts : t ≫ R.map prod.snd = prod.snd)
    (hV : muV = t ≫ R.map muY)
    (hB : L.map muV = prodComparison L X (R.obj Y) ≫
      prod.map er.inv i.inv ≫ muB ≫ i.hom) :
    muB ≫ i.hom ≫ a.counit.app Y =
      prod.map (𝟙 A) (i.hom ≫ a.counit.app Y) ≫ muY := by
  let q := prodComparison L X (R.obj Y) ≫ prod.map er.inv i.inv
  have hq : IsIso q := by dsimp only [q]; infer_instance
  have hp : L.map t ≫ a.counit.app (A ⨯ Y) =
      q ≫ prod.map (𝟙 A) (i.hom ≫ a.counit.app Y) := by
    apply prod.hom_ext
    · rw [Category.assoc, ← a.counit_naturality prod.fst,
        ← Category.assoc, ← L.map_comp, htf]
      dsimp only [q]
      simp only [Functor.map_comp, Category.assoc]
      rw [a.counit_naturality er.inv]
      simp
    · rw [Category.assoc, ← a.counit_naturality prod.snd,
        ← Category.assoc, ← L.map_comp, hts]
      dsimp only [q]
      simp
  apply (cancel_epi q).1
  rw [← Category.assoc muB i.hom, ← Category.assoc q (muB ≫ i.hom)]
  have hB' : L.map muV = q ≫ muB ≫ i.hom := by
    simpa only [q, Category.assoc] using hB
  rw [← hB', hV, L.map_comp, Category.assoc, a.counit_naturality muY,
    ← Category.assoc, hp, Category.assoc]

private noncomputable def moduleAction (U : Scheme.{u})
    (O : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj O) ⨯
      ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj M)) ⟶
      ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj M)) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @SMul.smul (O.obj.obj W) (M.val.obj W)
       (M.val.obj W).isModule.toSMul
       ((prod.fst : _ ⨯ _ ⟶
         ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj O)).hom.app W x)
       ((prod.snd : _ ⨯ _ ⟶
         ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
           ((SheafOfModules.toSheaf.{u + 1} _).obj M))).hom.app
           W x))
     naturality := by
       intro W W' f
       ext x
       have hf := ConcreteCategory.congr_hom ((prod.fst : _ ⨯ _ ⟶
         ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj O)).hom.naturality f) x
       have hs := ConcreteCategory.congr_hom ((prod.snd : _ ⨯ _ ⟶
         ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
           ((SheafOfModules.toSheaf.{u + 1} _).obj M))).hom.naturality f) x
       dsimp at hf hs ⊢
       rw [hf, hs]
       exact (M.val.map_smul f _ _).symm }⟩

private local instance presheafHasDiscreteLimits.{uC, uT} {C : Type uC} [Category C]
    (I : Type) : HasLimitsOfShape (Discrete I) (Cᵒᵖ ⥤ Type uT) :=
  functorCategoryHasLimitsOfShape

private local instance sheafHasDiscreteLimits.{uC, uT} {C : Type uC} [Category C]
    (J : GrothendieckTopology C) (I : Type) : HasLimitsOfShape (Discrete I) (Sheaf J (Type uT)) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J (Type uT))

private theorem product_sections.{uC, uT} {C : Type uC} [Category C] (J : GrothendieckTopology C)
    (A B : Sheaf J (Type uT)) (W : Cᵒᵖ) (r : A.obj.obj W) (m : B.obj.obj W) :
    ∃ x : (A ⨯ B).obj.obj W,
      (prod.fst : A ⨯ B ⟶ A).hom.app W x = r ∧
      (prod.snd : A ⨯ B ⟶ B).hom.app W x = m := by
  let E := sheafToPresheaf J (Type uT) ⋙ (evaluation Cᵒᵖ (Type uT)).obj W
  let e := PreservesLimitPair.iso E A B ≪≫ Types.binaryProductIso _ _
  let x := e.inv (r, m)
  refine ⟨x, ?_, ?_⟩
  · have h : e.inv ≫ E.map (prod.fst : A ⨯ B ⟶ A) = ↾Prod.fst := by
      dsimp only [e, Iso.trans_inv]
      rw [Category.assoc, PreservesLimitPair.iso_inv_fst,
        Types.binaryProductIso_inv_comp_fst]
    exact types_congr_hom h (r, m)
  · have h : e.inv ≫ E.map (prod.snd : A ⨯ B ⟶ B) = ↾Prod.snd := by
      dsimp only [e, Iso.trans_inv]
      rw [Category.assoc, PreservesLimitPair.iso_inv_snd,
        Types.binaryProductIso_inv_comp_snd]
    exact types_congr_hom h (r, m)

/-- The transported abelian counit admits a module lift.
Source: Stacks Project, Tag 03D3 (lemma-adjoint-push-pull-modules).
(blueprint: lem-weil-pbc-inverse-image-module-counit-linear-lift).

Proof:
1. Apply the transported-action hypothesis to RM(F). The ring and abelian
hom-equivalence equations identify their units with the set unit through er
and ea. Their inverse equations identify the counits with the set counit
through the same comparisons. The action on RM(F) is the direct image of
mu_F restricted along ar.unit_O, by the definition of pushforward.
2. Forget to sets and conjugate by the displayed comparisons. Naturality of
the set counit at mu_F reduces scalar compatibility to the identity
L(eta_O times id) followed by epsilon_(L(O) times F)
= lambda followed by (id times epsilon_F).
Check the two product projections: the first is
L(eta_O) followed by epsilon_(L(O)) followed by the scalar projection,
which equals the scalar projection by the left triangle identity; the second
is L of the module projection followed by epsilon_F, by counit naturality.
Substituting this identity and the transported-action equation proves that
e_(RM(F)) followed by the abelian counit is linear over Lr(O).
3. This composite is already an additive natural map. Build its sectionwise
linear maps with PresheafOfModules.homMk, using the scalar compatibility of
step 2, and wrap in SheafOfModules.Hom. Forgetting this lift gives exactly
the prescribed composite. -/
theorem etaleInverseImageModuleCounitLinearLift (U V : Scheme.{u}) (f : U ⟶ V)
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
      ∀ F : SheafOfModules.{u + 1} OR,
        ∃ h : LM.obj (RM.obj F) ⟶ F,
          FU.map h = e.hom.app (RM.obj F) ≫ a.counit.app (FU.obj F) := by
  intro L La a FaU FaV FrU FrV b aS Rr Lr ar er OR OV eta RM FV FU ea LM e H F
  obtain ⟨hr, ha, hM⟩ := H
  obtain ⟨muV, muU, hmuV, hmuU, hmu⟩ := hM (RM.obj F)
  let R := b.sheafPushforwardContinuous (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let X := FrV.obj O
  let A := FrU.obj (Lr.obj O)
  let Y := FaU.obj (FU.obj F)
  let B := FaU.obj (FU.obj (LM.obj (RM.obj F)))
  let i := (FaU.mapIso (e.app (RM.obj F))) ≪≫ ea.app (FV.obj (RM.obj F))
  let muF := moduleAction U (Lr.obj O) F
  let c := e.hom.app (RM.obj F) ≫ a.counit.app (FU.obj F)
  have hη : FrV.map (ar.unit.app O) = aS.unit.app X ≫ R.map (er.inv.app O) := by
    have hh := hr O (Lr.obj O) (𝟙 _)
    rw [ar.homEquiv_id, aS.homEquiv_apply] at hh
    simpa using hh
  have hε : ea.inv.app (FV.obj (RM.obj F)) ≫ FaU.map (a.counit.app (FU.obj F)) =
      aS.counit.app Y := by
    apply (aS.homEquiv _ _).injective
    rw [← ha]
    change FaV.map (a.homEquiv _ _ (a.counit.app (FU.obj F))) =
      aS.homEquiv _ _ (aS.counit.app (FaU.obj (FU.obj F)))
    simp +instances [← a.homEquiv_symm_id, ← aS.homEquiv_symm_id]
    rfl
  have hc : FaU.map c = i.hom ≫ aS.counit.app Y := by
    dsimp only [c, i, Iso.trans_hom, Functor.mapIso_hom]
    rw [FaU.map_comp, ← hε]
    simp
  let unitO : X ⟶ R.obj A := FrV.map (ar.unit.app O)
  let t : X ⨯ R.obj Y ⟶ R.obj (A ⨯ Y) :=
    prod.lift (prod.fst ≫ unitO) prod.snd ≫
      inv (prodComparison R A Y)
  have htf : t ≫ R.map prod.fst = prod.fst ≫ aS.unit.app X ≫ R.map (er.inv.app O) := by
    dsimp only [t]
    rw [Category.assoc, inv_prodComparison_map_fst]
    rw [prod.lift_fst]
    exact congrArg (fun z : X ⟶ R.obj A ↦ (prod.fst : X ⨯ R.obj Y ⟶ X) ≫ z) hη
  have hts : t ≫ R.map prod.snd = prod.snd := by
    dsimp only [t]
    rw [Category.assoc, inv_prodComparison_map_snd]
    exact prod.lift_snd _ _
  have hV : muV = t ≫ R.map muF := by
    ext W x
    have htf' : t ≫ R.map prod.fst = prod.fst ≫ FrV.map (ar.unit.app O) := by
      exact htf.trans (congrArg
        (fun z : X ⟶ R.obj A ↦ (prod.fst : X ⨯ R.obj Y ⟶ X) ≫ z) hη.symm)
    have hf := types_congr_hom
      (congrArg (fun k : X ⨯ R.obj Y ⟶ R.obj A ↦ k.hom.app W)
        htf') x
    have hs := types_congr_hom
      (congrArg (fun k : X ⨯ R.obj Y ⟶ R.obj Y ↦ k.hom.app W) hts) x
    change (prod.fst : A ⨯ Y ⟶ A).hom.app (b.op.obj W) (t.hom.app W x) =
      (ar.unit.app O).hom.app W ((prod.fst : X ⨯ R.obj Y ⟶ X).hom.app W x) at hf
    change (prod.snd : A ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (prod.snd : X ⨯ R.obj Y ⟶ R.obj Y).hom.app W x at hs
    change muV.hom.app W x = muF.hom.app (b.op.obj W) (t.hom.app W x)
    erw [hmuV W x]
    change _ = @SMul.smul (OR.obj.obj (b.op.obj W)) (F.val.obj (b.op.obj W))
      (F.val.obj (b.op.obj W)).isModule.toSMul
      ((prod.fst : A ⨯ Y ⟶ A).hom.app (b.op.obj W) (t.hom.app W x))
      ((prod.snd : A ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hf, hs]
    rfl
  have hL : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback b (Type (u + 1))
        (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)) :=
    (etaleInverseImageAlgebraicStructures U V f).1
  have haction := counit_action aS X A B Y (er.app O) i muV muU muF t htf hts hV hmu
  rw [← hc] at haction
  have hlinear : ∀ (W : U.Etaleᵒᵖ) (r : OR.obj.obj W)
      (m : (LM.obj (RM.obj F)).val.obj W),
      c.hom.app W (r • m) =
        @SMul.smul (OR.obj.obj W) (F.val.obj W) (F.val.obj W).isModule.toSMul r
          (c.hom.app W m) := by
    intro W r m
    obtain ⟨x, hx₁, hx₂⟩ := product_sections U.smallEtaleTopology A B W r m
    let z := (prod.map (𝟙 A) (FaU.map c)).hom.app W x
    have hz₁ : (prod.fst : A ⨯ Y ⟶ A).hom.app W z = r := by
      have hh := types_congr_hom
        (congrArg (fun k : A ⨯ B ⟶ A ↦ k.hom.app W)
          (prod.map_fst (𝟙 A) (FaU.map c))) x
      change (prod.fst : A ⨯ Y ⟶ A).hom.app W z =
        (prod.fst : A ⨯ B ⟶ A).hom.app W x at hh
      exact hh.trans hx₁
    have hz₂ : (prod.snd : A ⨯ Y ⟶ Y).hom.app W z = c.hom.app W m := by
      have hh := types_congr_hom
        (congrArg (fun k : A ⨯ B ⟶ Y ↦ k.hom.app W)
          (prod.map_snd (𝟙 A) (FaU.map c))) x
      change (prod.snd : A ⨯ Y ⟶ Y).hom.app W z =
        c.hom.app W ((prod.snd : A ⨯ B ⟶ B).hom.app W x) at hh
      exact hh.trans (congrArg (fun q ↦ c.hom.app W q) hx₂)
    have hh := types_congr_hom
      (congrArg (fun k : A ⨯ B ⟶ Y ↦ k.hom.app W) haction) x
    change c.hom.app W (muU.hom.app W x) = muF.hom.app W z at hh
    erw [hmuU W x] at hh
    change c.hom.app W (@SMul.smul (OR.obj.obj W) ((LM.obj (RM.obj F)).val.obj W)
      ((LM.obj (RM.obj F)).val.obj W).isModule.toSMul
      ((prod.fst : A ⨯ B ⟶ A).hom.app W x) ((prod.snd : A ⨯ B ⟶ B).hom.app W x)) =
        @SMul.smul (OR.obj.obj W) (F.val.obj W) (F.val.obj W).isModule.toSMul
          ((prod.fst : A ⨯ Y ⟶ A).hom.app W z) ((prod.snd : A ⨯ Y ⟶ Y).hom.app W z) at hh
    rw [hx₁, hx₂, hz₁, hz₂] at hh
    exact hh
  refine ⟨⟨PresheafOfModules.homMk c.hom hlinear⟩, ?_⟩
  rfl

end AlgebraicGeometry
