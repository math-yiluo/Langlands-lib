/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
/-! # The transported abelian unit lifts to a module map

Source: Stacks Project, Tag 03D3
(blueprint: lem-weil-pbc-inverse-image-module-unit-linear-lift). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem adjunct_action
    {C D : Type*} [Category C] [Category D]
    [HasBinaryProducts C] [HasBinaryProducts D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {O M : C} {O' M' : D} (er : O' ≅ L.obj O) (i : M' ≅ L.obj M)
    (mu : O ⨯ M ⟶ M) (mu' : O' ⨯ M' ⟶ M')
    (h : L.map mu = prodComparison L O M ≫ prod.map er.inv i.inv ≫ mu' ≫ i.hom) :
    mu ≫ a.homEquiv M M' i.inv =
      a.homEquiv (O ⨯ M) (O' ⨯ M')
        (prodComparison L O M ≫ prod.map er.inv i.inv) ≫ R.map mu' := by
  rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right]
  congr 1
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem adjunct_pair_fst
    {C D : Type*} [Category C] [Category D]
    [HasBinaryProducts C] [HasBinaryProducts D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {O M : C} {O' M' : D} (er : O' ≅ L.obj O) (i : M' ≅ L.obj M) :
    a.homEquiv (O ⨯ M) (O' ⨯ M')
        (prodComparison L O M ≫ prod.map er.inv i.inv) ≫ R.map prod.fst =
      prod.fst ≫ a.homEquiv O O' er.inv := by
  rw [← a.homEquiv_naturality_right]
  rw [Category.assoc, prod.map_fst, ← Category.assoc, prodComparison_fst]
  exact a.homEquiv_naturality_left _ _

private theorem adjunct_pair_snd
    {C D : Type*} [Category C] [Category D]
    [HasBinaryProducts C] [HasBinaryProducts D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {O M : C} {O' M' : D} (er : O' ≅ L.obj O) (i : M' ≅ L.obj M) :
    a.homEquiv (O ⨯ M) (O' ⨯ M')
        (prodComparison L O M ≫ prod.map er.inv i.inv) ≫ R.map prod.snd =
      prod.snd ≫ a.homEquiv M M' i.inv := by
  rw [← a.homEquiv_naturality_right]
  rw [Category.assoc, prod.map_snd, ← Category.assoc, prodComparison_snd]
  exact a.homEquiv_naturality_left _ _

/-- The transported abelian unit admits a module lift.
Source: Stacks Project, Tag 03D3 (lemma-adjoint-push-pull-modules).
(blueprint: lem-weil-pbc-inverse-image-module-unit-linear-lift).

Proof:
1. Write t for the set adjunct of i_G.inv, where i_G is the displayed composite
comparison. The abelian hom-equivalence compatibility identifies the underlying
map of a(e_G.inv) with t. The ring compatibility at the identity identifies
ar.unit at O with the set unit at O followed by R(er_O.inv).
2. Naturality of the set unit at mu_G gives eta_G composed with R(L(mu_G))
equal to mu_G composed with eta_(O times G). Substitute the transported-action
equation. The product-comparison equation
eta_(O times G) followed by R(lambda) = eta_O times eta_G follows by
composing with each projection and applying unit naturality. Cancel i_G
against its inverse. The resulting equality says exactly that t sends r times x
to the action of ar.unit_O(r) on t(x).
3. The abelian adjunct is already additive and natural in the site object.
The scalar equality in step 2 makes each component linear for the restricted
scalar action on RM(LM(G)). Apply PresheafOfModules.homMk to its underlying
abelian presheaf map and wrap it in SheafOfModules.Hom. Its underlying abelian
map is unchanged, giving the stated equation. -/
theorem etaleInverseImageModuleUnitLinearLift (U V : Scheme.{u}) (f : U ⟶ V)
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
      ∀ G : SheafOfModules.{u + 1} OV,
        ∃ k : G ⟶ RM.obj (LM.obj G),
          FV.map k = a.homEquiv (FV.obj G) (FU.obj (LM.obj G)) (e.inv.app G) := by
  intro L La a FaU FaV FrU FrV b aS Rr Lr ar er OR OV eta RM FV FU ea LM e H G
  obtain ⟨hr, ha, hmu⟩ := H
  obtain ⟨muV, muU, hV, hU, htransport⟩ := hmu G
  let q := a.homEquiv (FV.obj G) (FU.obj (LM.obj G)) (e.inv.app G)
  refine ⟨⟨PresheafOfModules.homMk q.hom ?_⟩, ?_⟩
  · intro W r m
    let iG := (FaU.mapIso (e.app G)) ≪≫ ea.app (FV.obj G)
    have hq : FaV.map q = aS.homEquiv _ _ iG.inv := by
      change FaV.map q = aS.homEquiv _ _
        (ea.inv.app (FV.obj G) ≫ FaU.map (e.inv.app G))
      exact ha (FV.obj G) (FU.obj (LM.obj G)) (e.inv.app G)
    have hr' : FrV.map (ar.unit.app O) = aS.homEquiv _ _ (er.inv.app O) := by
      have hr0 := hr O (Lr.obj O) (𝟙 _)
      rw [ar.homEquiv_id] at hr0
      simpa using hr0
    have hact := adjunct_action aS (er.app O) iG muV muU htransport
    let E := sheafToPresheaf V.smallEtaleTopology (Type (u + 1)) ⋙
      (CategoryTheory.evaluation V.Etaleᵒᵖ (Type (u + 1))).obj W
    let x := (inv (prodComparison E (FrV.obj O) (FaV.obj (FV.obj G))))
      ((Types.binaryProductIso _ _).inv (r, m))
    have hx₁ : (prod.fst : FrV.obj O ⨯ FaV.obj (FV.obj G) ⟶
        FrV.obj O).hom.app W x = r := by
      change (E.map prod.fst) x = r
      dsimp only [x]
      rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_fst]
      simp
    have hx₂ : (prod.snd : FrV.obj O ⨯ FaV.obj (FV.obj G) ⟶
        FaV.obj (FV.obj G)).hom.app W x = m := by
      change (E.map prod.snd) x = m
      dsimp only [x]
      rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_snd]
      simp
    let R := b.sheafPushforwardContinuous (Type (u + 1))
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let p := aS.homEquiv (FrV.obj O ⨯ FaV.obj (FV.obj G))
      (FrU.obj (Lr.obj O) ⨯ FaU.obj (FU.obj (LM.obj G)))
      (prodComparison L (FrV.obj O) (FaV.obj (FV.obj G)) ≫
        prod.map (er.inv.app O) iG.inv)
    have hp₁ : p ≫ R.map prod.fst = prod.fst ≫ FrV.map (ar.unit.app O) := by
      rw [hr']
      exact adjunct_pair_fst aS (er.app O) iG
    have hp₂ : p ≫ R.map prod.snd = prod.snd ≫ FaV.map q := by
      rw [hq]
      exact adjunct_pair_snd aS (er.app O) iG
    have hact' : muV ≫ FaV.map q = p ≫ R.map muU := by
      rw [hq]
      exact hact
    have hxact := congrArg (fun k ↦ (k.hom.app W) x) hact'
    have hxp₁ := congrArg (fun k ↦ (k.hom.app W) x) hp₁
    have hxp₂ := congrArg (fun k ↦ (k.hom.app W) x) hp₂
    change q.hom.app W (muV.hom.app W x) =
      muU.hom.app (b.op.obj W) (p.hom.app W x) at hxact
    change (prod.fst : FrU.obj (Lr.obj O) ⨯ FaU.obj (FU.obj (LM.obj G)) ⟶
      FrU.obj (Lr.obj O)).hom.app (b.op.obj W) (p.hom.app W x) =
      (ar.unit.app O).hom.app W
        ((prod.fst : FrV.obj O ⨯ FaV.obj (FV.obj G) ⟶ FrV.obj O).hom.app W x)
      at hxp₁
    change (prod.snd : FrU.obj (Lr.obj O) ⨯ FaU.obj (FU.obj (LM.obj G)) ⟶
      FaU.obj (FU.obj (LM.obj G))).hom.app (b.op.obj W) (p.hom.app W x) =
      q.hom.app W ((prod.snd : FrV.obj O ⨯ FaV.obj (FV.obj G) ⟶
        FaV.obj (FV.obj G)).hom.app W x) at hxp₂
    rw [hV W x, hx₁, hx₂, hU (b.op.obj W) (p.hom.app W x),
      hxp₁, hxp₂, hx₁, hx₂] at hxact
    exact hxact
  · rfl

end AlgebraicGeometry
