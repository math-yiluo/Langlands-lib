/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
/-! # Transporting modules through the etale inverse image

Source: Stacks Project, Tags 03D1 and 03D2
(blueprint: lem-weil-pbc-inverse-image-module-map-linearity). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private local instance sheafTypesHasBinaryProduct.{uC, vC, w}
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (X Y : Sheaf J (Type w)) : HasBinaryProduct X Y :=
  have : HasBinaryProducts (Sheaf J (Type w)) := Sheaf.instHasLimitsOfShape
  HasLimitsOfShape.has_limit _

private theorem transport_action_square
    {C : Type*} [Category C] [HasBinaryProducts C]
    {D : Type*} [Category D] [HasBinaryProducts D]
    (L : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) L]
    {R X Y : C} {S X' Y' : D}
    (r : L.obj R ≅ S) (i : X' ≅ L.obj X) (j : Y' ≅ L.obj Y)
    (v : X ⟶ Y) (w : X' ⟶ Y')
    (muX : R ⨯ X ⟶ X) (muY : R ⨯ Y ⟶ Y)
    (muX' : S ⨯ X' ⟶ X') (muY' : S ⨯ Y' ⟶ Y')
    (hX : L.map muX = prodComparison L R X ≫ prod.map r.hom i.inv ≫ muX' ≫ i.hom)
    (hY : L.map muY = prodComparison L R Y ≫ prod.map r.hom j.inv ≫ muY' ≫ j.hom)
    (hv : muX ≫ v = prod.map (𝟙 R) v ≫ muY)
    (hw : i.hom ≫ L.map v = w ≫ j.hom) :
    muX' ≫ w = prod.map (𝟙 S) w ≫ muY' := by
  have hn : prod.map r.hom i.inv ≫ prod.map (𝟙 S) w =
      prod.map (𝟙 (L.obj R)) (L.map v) ≫ prod.map r.hom j.inv := by
    have hh : i.inv ≫ w = L.map v ≫ j.inv := by
      apply (cancel_epi i.hom).mp
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ j.inv) hw.symm
    ext <;> simp [hh]
  apply (cancel_epi (prodComparison L R X ≫ prod.map r.hom i.inv)).mp
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc]
  calc
    prodComparison L R X ≫ prod.map r.hom i.inv ≫ muX' ≫ w ≫ j.hom =
        L.map muX ≫ L.map v := by
      rw [hX]
      simpa only [Category.assoc] using
        congrArg (fun t ↦ prodComparison L R X ≫ prod.map r.hom i.inv ≫ muX' ≫ t) hw.symm
    _ = L.map (prod.map (𝟙 R) v) ≫ L.map muY := by
      rw [← L.map_comp, hv, L.map_comp]
    _ = prodComparison L R X ≫ prod.map r.hom i.inv ≫
        prod.map (𝟙 S) w ≫ muY' ≫ j.hom := by
      rw [hY]
      rw [prodComparison_natural_assoc]
      simp only [L.map_id]
      rw [← reassoc_of% hn]

private theorem section_pair
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (A B : Sheaf J (Type u)) (W : Cᵒᵖ)
    (a : A.obj.obj W) (b : B.obj.obj W) :
    ∃ x : (A ⨯ B).obj.obj W,
      (prod.fst : A ⨯ B ⟶ A).hom.app W x = a ∧
      (prod.snd : A ⨯ B ⟶ B).hom.app W x = b := by
  let E := sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj W
  let l := isLimitOfHasBinaryProductOfPreservesLimit E A B
  let p : PUnit.{u + 1} ⟶ E.obj A := ↾(fun _ ↦ a)
  let q : PUnit.{u + 1} ⟶ E.obj B := ↾(fun _ ↦ b)
  refine ⟨(BinaryFan.IsLimit.lift l p q) PUnit.unit, ?_, ?_⟩
  · exact CategoryTheory.congr_fun (BinaryFan.IsLimit.lift_fst l p q) PUnit.unit
  · exact CategoryTheory.congr_fun (BinaryFan.IsLimit.lift_snd l p q) PUnit.unit

/-- Pullback of a linear map is linear for any objectwise transported scalar actions.
Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module; the morphism part of
lem-weil-pbc-inverse-image-module-construction, step 1(a).
(blueprint: lem-weil-pbc-inverse-image-module-map-linearity).

Proof: the original scalar-action morphisms satisfy the linearity square because
phi is sectionwise linear. Apply the set pullback to this square. Substitute the
two assumed transport equations. Naturality of prodComparison, of ea, and of the
conjugation by the abelian comparisons d identifies the resulting square with the square
for g. Cancel the invertible product comparison and the ring and group comparisons.
This gives mu_G followed by g = (id times g) followed by mu_G'. Evaluate on sections;
finite products of set sheaves are sectionwise, so apply this equality to the pair
(r,m). The section formulas for mu_G and mu_G' give exactly the displayed scalar
linearity equation. This statement asserts no module-object existence and no
functoriality; its conclusion concerns only a given map and given objects. -/
theorem etaleInverseImageModuleMapLinearity (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}) :
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    ∀ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
        Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (er : Lr ⋙ FrU ≅ FrV ⋙ L),
    let OR := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
    let OV := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    let FU := SheafOfModules.toSheaf.{u + 1} OR
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
    ∀ (H : SheafOfModules.{u + 1} OV → SheafOfModules.{u + 1} OR)
      (d : ∀ G, FU.obj (H G) ≅ La.obj (FV.obj G)),
      (∀ G : SheafOfModules.{u + 1} OV,
        let iG := (FaU.mapIso (d G)) ≪≫ ea.app (FV.obj G)
        ∃ (muV : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶ FaV.obj (FV.obj G))
          (muU : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (H G))) ⟶
            FaU.obj (FU.obj (H G))),
          (∀ (W : V.Etaleᵒᵖ)
              (x : ((FrV.obj O) ⨯ (FaV.obj (FV.obj G))).obj.obj W),
            muV.hom.app W x =
              @SMul.smul (OV.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
              ((prod.fst : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FrV.obj O).hom.app W x : OV.obj.obj W)
              ((prod.snd : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FaV.obj (FV.obj G)).hom.app W x : G.val.obj W)) ∧
          (∀ (W : U.Etaleᵒᵖ)
              (x : ((FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (H G)))).obj.obj W),
            muU.hom.app W x =
              @SMul.smul (OR.obj.obj W) ((H G).val.obj W)
                ((H G).val.obj W).isModule.toSMul
              ((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (H G))) ⟶
                FrU.obj (Lr.obj O)).hom.app W x : OR.obj.obj W)
              ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (H G))) ⟶
                FaU.obj (FU.obj (H G))).hom.app W x : (H G).val.obj W)) ∧
          L.map muV = prodComparison L (FrV.obj O) (FaV.obj (FV.obj G)) ≫
            prod.map (er.inv.app O) iG.inv ≫ muU ≫ iG.hom) →
      ∀ (G G' : SheafOfModules.{u + 1} OV) (φ : G ⟶ G')
        (W : U.Etaleᵒᵖ) (r : OR.obj.obj W) (m : (H G).val.obj W),
        let g := (d G).hom ≫ La.map (FV.map φ) ≫ (d G').inv
        g.hom.app W
          (@SMul.smul (OR.obj.obj W) ((H G).val.obj W)
            ((H G).val.obj W).isModule.toSMul r m) =
          @SMul.smul (OR.obj.obj W) ((H G').val.obj W)
            ((H G').val.obj W).isModule.toSMul r (g.hom.app W m) := by
  classical
  dsimp only
  intro Lr er ea H d hact G G' φ W r m
  let L := Scheme.etaleSetPullback f
  let La := Etale.upperStar AddCommGrpCat.{u + 1} f
  let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
  let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
  let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
  let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
  let OR := (sheafCompose U.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
  let OV := (sheafCompose V.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let FU := SheafOfModules.toSheaf.{u + 1} OR
  let FV := SheafOfModules.toSheaf.{u + 1} OV
  let i := (FaU.mapIso (d G)) ≪≫ ea.app (FV.obj G)
  let j := (FaU.mapIso (d G')) ≪≫ ea.app (FV.obj G')
  let v := FaV.map (FV.map φ)
  let g := (d G).hom ≫ La.map (FV.map φ) ≫ (d G').inv
  let w := FaU.map g
  obtain ⟨muX, muX', hvX, huX, htX⟩ := hact G
  obtain ⟨muY, muY', hvY, huY, htY⟩ := hact G'
  have hv : muX ≫ v = prod.map (𝟙 (FrV.obj O)) v ≫ muY := by
    ext Z x
    have hp := CategoryTheory.congr_fun
      (congr_app (congrArg (fun t ↦ t.hom)
        (prod.map_fst (𝟙 (FrV.obj O)) v)) Z) x
    have hq := CategoryTheory.congr_fun
      (congr_app (congrArg (fun t ↦ t.hom)
        (prod.map_snd (𝟙 (FrV.obj O)) v)) Z) x
    change v.hom.app Z (muX.hom.app Z x) =
      muY.hom.app Z ((prod.map (𝟙 (FrV.obj O)) v).hom.app Z x)
    rw [hvX, hvY]
    dsimp at hp hq
    rw [hp, hq]
    exact (φ.val.app Z).hom.map_smul _ _
  have hw : i.hom ≫ L.map v = w ≫ j.hom := by
    dsimp only [i, j, w, g, Iso.trans_hom, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [← FaU.map_comp_assoc (d G').inv (d G').hom,
      (d G').inv_hom_id, FaU.map_id]
    simp only [Category.id_comp]
    exact congrArg (fun t ↦ FaU.map (d G).hom ≫ t) (ea.hom.naturality (FV.map φ)).symm
  have hL := (etaleInverseImageAlgebraicStructures U V f).1
  let : PreservesFiniteLimits L := hL
  have ht := transport_action_square L (er.app O).symm i j v w
    muX muY muX' muY' htX htY hv hw
  obtain ⟨x, hx, hy⟩ := section_pair U.smallEtaleTopology
    (FrU.obj (Lr.obj O)) (FaU.obj (FU.obj (H G))) W r m
  have hh := CategoryTheory.congr_fun (congr_app (congrArg (fun t ↦ t.hom) ht) W) x
  have hp := CategoryTheory.congr_fun
    (congr_app (congrArg (fun t ↦ t.hom)
      (prod.map_fst (𝟙 (FrU.obj (Lr.obj O))) w)) W) x
  have hq := CategoryTheory.congr_fun
    (congr_app (congrArg (fun t ↦ t.hom)
      (prod.map_snd (𝟙 (FrU.obj (Lr.obj O))) w)) W) x
  change w.hom.app W (muX'.hom.app W x) =
    muY'.hom.app W ((prod.map (𝟙 (FrU.obj (Lr.obj O))) w).hom.app W x) at hh
  rw [huX, huY] at hh
  dsimp at hp hq
  rw [hp, hq, hx, hy] at hh
  exact hh


end AlgebraicGeometry
