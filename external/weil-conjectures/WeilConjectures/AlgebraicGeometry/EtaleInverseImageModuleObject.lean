/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleActionLaws
import Mathlib.CategoryTheory.Limits.Types.Products
/-! # Transporting modules through the etale inverse image

Source: Stacks Project, Tags 03D1 and 03D2
(blueprint: lem-weil-pbc-inverse-image-module-object). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def sectionProdIso (V : Scheme.{u})
    (R A : Sheaf V.smallEtaleTopology (Type (u + 1))) (W : V.Etaleᵒᵖ) :
    (R ⨯ A).obj.obj W ≅ R.obj.obj W × A.obj.obj W :=
  asIso (prodComparison (sheafToPresheaf V.smallEtaleTopology (Type (u + 1)) ⋙
    (evaluation _ _).obj W) R A) ≪≫ Types.binaryProductIso _ _
private theorem sectionProdIso_fst (V : Scheme.{u})
    (R A : Sheaf V.smallEtaleTopology (Type (u + 1)))
    (W : V.Etaleᵒᵖ) (r : R.obj.obj W) (x : A.obj.obj W) :
    (prod.fst : R ⨯ A ⟶ R).hom.app W ((sectionProdIso V R A W).inv (r,x)) = r := by
  have h : (sectionProdIso V R A W).inv ≫
      (prod.fst : R ⨯ A ⟶ R).hom.app W = ↾(fun p : R.obj.obj W × A.obj.obj W ↦ p.1) := by
    change (Types.binaryProductIso _ _).inv ≫
      inv (prodComparison (sheafToPresheaf V.smallEtaleTopology (Type (u + 1)) ⋙
        (evaluation _ _).obj W) R A) ≫
        (sheafToPresheaf V.smallEtaleTopology (Type (u + 1)) ⋙
          (evaluation _ _).obj W).map prod.fst = _
    rw [inv_prodComparison_map_fst, Types.binaryProductIso_inv_comp_fst]
    rfl
  exact congrArg (fun k : R.obj.obj W × A.obj.obj W ⟶ R.obj.obj W ↦ k (r,x)) h

private theorem sectionProdIso_snd (V : Scheme.{u})
    (R A : Sheaf V.smallEtaleTopology (Type (u + 1)))
    (W : V.Etaleᵒᵖ) (r : R.obj.obj W) (x : A.obj.obj W) :
    (prod.snd : R ⨯ A ⟶ A).hom.app W ((sectionProdIso V R A W).inv (r,x)) = x := by
  have h : (sectionProdIso V R A W).inv ≫
      (prod.snd : R ⨯ A ⟶ A).hom.app W = ↾(fun p : R.obj.obj W × A.obj.obj W ↦ p.2) := by
    change (Types.binaryProductIso _ _).inv ≫
      inv (prodComparison (sheafToPresheaf V.smallEtaleTopology (Type (u + 1)) ⋙
        (evaluation _ _).obj W) R A) ≫
        (sheafToPresheaf V.smallEtaleTopology (Type (u + 1)) ⋙
          (evaluation _ _).obj W).map prod.snd = _
    rw [inv_prodComparison_map_snd, Types.binaryProductIso_inv_comp_snd]
    rfl
  exact congrArg (fun k : R.obj.obj W × A.obj.obj W ⟶ A.obj.obj W ↦ k (r,x)) h

/-- Objectwise transport of the scalar action, before constructing maps or a functor.
Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module; the object part of
lem-weil-pbc-inverse-image-module-construction, step 1(a).
(blueprint: lem-weil-pbc-inverse-image-module-object).

Proof: identify the specified ring and abelian comparisons with the canonical lifts
using the hom-equivalence equations and uniqueness of left adjoints. The set pullback
preserves finite products. Apply it to the scalar action of G and conjugate by the
product comparison and er and ea. Apply it to each module law: the two distributive
laws, multiplication associativity, and the unit law. The transported ring and
abelian operations make these precisely the module laws on the abelian pullback.
Naturality of the transported action makes restriction maps semilinear. Thus these
section modules form HG; its underlying abelian sheaf is the abelian pullback, giving
eG. The original and transported action morphisms have the stated section values,
and their definition gives the product-comparison equation. No choice of maps
between different modules, nor functoriality, is claimed here. -/
theorem etaleInverseImageModuleObject (U V : Scheme.{u}) (f : U ⟶ V)
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
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    let FU := SheafOfModules.toSheaf.{u + 1} OR
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
    ∀ G : SheafOfModules.{u + 1} OV,
    ∃ (HG : SheafOfModules.{u + 1} OR) (eG : FU.obj HG ≅ La.obj (FV.obj G)),
      let iG := (FaU.mapIso eG) ≪≫ ea.app (FV.obj G)
        ∃ (muV : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶ FaV.obj (FV.obj G))
          (muU : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj HG)) ⟶
            FaU.obj (FU.obj HG)),
          (∀ (W : V.Etaleᵒᵖ)
              (x : ((FrV.obj O) ⨯ (FaV.obj (FV.obj G))).obj.obj W),
            muV.hom.app W x =
              @SMul.smul (OV.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
              ((prod.fst : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FrV.obj O).hom.app W x : OV.obj.obj W)
              ((prod.snd : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FaV.obj (FV.obj G)).hom.app W x : G.val.obj W)) ∧
          (∀ (W : U.Etaleᵒᵖ)
              (x : ((FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj HG))).obj.obj W),
            muU.hom.app W x =
              @SMul.smul (OR.obj.obj W) (HG.val.obj W)
                (HG.val.obj W).isModule.toSMul
              ((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj HG)) ⟶
                FrU.obj (Lr.obj O)).hom.app W x : OR.obj.obj W)
              ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj HG)) ⟶
                FaU.obj (FU.obj HG)).hom.app W x : HG.val.obj W)) ∧
          L.map muV = prodComparison L (FrV.obj O) (FaV.obj (FV.obj G)) ≫
            prod.map (er.inv.app O) iG.inv ≫ muU ≫ iG.hom := by
  dsimp only
  intro Lr ar er ea h G
  let : PreservesFiniteLimits (Scheme.etaleSetPullback f) :=
    (etaleInverseImageAlgebraicStructures U V f).1
  obtain ⟨m, hm⟩ := etaleInverseImageModuleActionLaws U V f O Lr ar er ea h G
  let A := (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
    ((SheafOfModules.toSheaf _).obj G)
  let OR := (sheafCompose U.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
  let (W : U.Etaleᵒᵖ) : Module (OR.obj.obj W) (A.obj.obj W) := m W
  let mu := prod.map (er.hom.app O) (ea.hom.app ((SheafOfModules.toSheaf _).obj G)) ≫
    inv (prodComparison (Scheme.etaleSetPullback f)
      ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj O)
      ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf _).obj G))) ≫
    (Scheme.etaleSetPullback f).map (etaleModuleScalarAction V O G) ≫
      ea.inv.app ((SheafOfModules.toSheaf _).obj G)
  have linear : ∀ ⦃W Z : U.Etaleᵒᵖ⦄ (i : W ⟶ Z)
      (r : OR.obj.obj W) (x : A.obj.obj W),
      A.obj.map i (r • x) = OR.obj.map i r • A.obj.map i x := by
    intro W Z i r x
    let y := (sectionProdIso U
      ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj O))
      ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj A) W).inv
      (r, x)
    have hW := hm W y
    have hZ := hm Z (((sheafForget (D := CommRingCat.{u + 1})
      U.smallEtaleTopology).obj (Lr.obj O) ⨯
      (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj A).obj.map i y)
    have hn := ConcreteCategory.congr_hom (mu.hom.naturality i) y
    have hf := ConcreteCategory.congr_hom
      ((prod.fst : _ ⟶ (sheafForget (D := CommRingCat.{u + 1})
        U.smallEtaleTopology).obj (Lr.obj O)).hom.naturality i) y
    have hs := ConcreteCategory.congr_hom
      ((prod.snd : _ ⟶ (sheafForget (D := AddCommGrpCat.{u + 1})
        U.smallEtaleTopology).obj A).hom.naturality i) y
    dsimp at hn hf hs
    have hf0 := sectionProdIso_fst U
      ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj O))
      ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj A) W r x
    have hs0 := sectionProdIso_snd U
      ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj O))
      ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj A) W r x
    rw [hf0, hs0] at hW
    erw [hf0] at hf
    erw [hs0] at hs
    erw [hf, hs] at hZ
    exact (congrArg (fun z ↦ A.obj.map i z) hW).trans (hn.symm.trans hZ.symm)
  let HG : SheafOfModules.{u + 1} OR :=
    ⟨PresheafOfModules.ofPresheaf A.obj linear, A.property⟩
  let eG : (SheafOfModules.toSheaf OR).obj HG ≅ A := Iso.refl _
  refine ⟨HG, eG, etaleModuleScalarAction V O G,
    etaleModuleScalarAction U (Lr.obj O) HG, ?_, ?_, ?_⟩
  · intro W x
    rfl
  · intro W x
    rfl
  · have heq : etaleModuleScalarAction U (Lr.obj O) HG = mu := by
      ext W x
      exact hm W x
    change (Scheme.etaleSetPullback f).map (etaleModuleScalarAction V O G) =
      prodComparison (Scheme.etaleSetPullback f)
        ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj O)
        ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
          ((SheafOfModules.toSheaf _).obj G)) ≫
      prod.map (er.inv.app O) (ea.inv.app ((SheafOfModules.toSheaf _).obj G)) ≫
      etaleModuleScalarAction U (Lr.obj O) HG ≫ ea.hom.app ((SheafOfModules.toSheaf _).obj G)
    rw [heq]
    simp [mu, ← Category.assoc, prod.map_map]
    simp [Category.assoc]

end AlgebraicGeometry
