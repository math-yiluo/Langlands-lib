/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Etale.EtaleInverseImageCompositionModuleLinearCore

/-!
# Linearity of the composition comparisons on constant-ring etale modules

## References

* Stacks Project, Modules on Sites, Tags 03D8 and 03D7

## Implementation details

In `etaleInverseImageCompositionModuleLinear`, the gamma maps are characterized by constant
sections, and the inverse images, comparison maps and adjunctions are the data of
`etaleInverseImageModulesExact`; the hom-equivalence equations say that these are the module
adjunctions with the underlying abelian adjunctions.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The unit equation uniquely determines an isomorphism of left adjoints. -/
private theorem exists_comparison_with_unique_unit
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {P P' : D ⥤ C} (a : L ⊣ P) (a' : L' ⊣ P')
    (p : (P' ≅ P) → Prop) (q : (L ≅ L') → Prop)
    (h : ∃ (d : P' ≅ P) (c : L ≅ L'), p d ∧ q c ∧
      ∀ G, a.unit.app G ≫ P.map (c.hom.app G) =
        a'.unit.app G ≫ d.hom.app (L'.obj G)) :
    ∃ (d : P' ≅ P) (c : L ≅ L'), p d ∧ q c ∧
      (∀ G, a.unit.app G ≫ P.map (c.hom.app G) =
        a'.unit.app G ≫ d.hom.app (L'.obj G)) ∧
      (∀ c' : L ≅ L',
        (∀ G, a.unit.app G ≫ P.map (c'.hom.app G) =
          a'.unit.app G ≫ d.hom.app (L'.obj G)) → c' = c) := by
  obtain ⟨d, c, hd, hc, hu⟩ := h
  refine ⟨d, c, hd, hc, hu, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply (a.homEquiv G (L'.obj G)).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  exact (hc' G).trans (hu G).symm

set_option backward.defeqAttrib.useBackward true in
/-- The abelian composition comparisons lift to module isomorphisms, uniquely for inverse
image with the specified unit equation. -/
theorem etaleInverseImageCompositionModuleLinear
    (X Y Z : Scheme.{u}) (uMap : Y ⟶ X) (vMap : Z ⟶ Y) (R : CommRingCat.{u + 1}) :
    (fun (RX : Sheaf (X.smallGrothendieckTopology @Etale) CommRingCat.{u + 1})
      (RY : Sheaf (Y.smallGrothendieckTopology @Etale) CommRingCat.{u + 1})
      (RZ : Sheaf (Z.smallGrothendieckTopology @Etale) CommRingCat.{u + 1})
      (etaX : ((Functor.const X.Etaleᵒᵖ).obj R) ⟶ RX.obj)
      (etaY : ((Functor.const Y.Etaleᵒᵖ).obj R) ⟶ RY.obj)
      (etaZ : ((Functor.const Z.Etaleᵒᵖ).obj R) ⟶ RZ.obj) =>
    ∀ (gammaU : RX ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ uMap).sheafPushforwardContinuous
      CommRingCat.{u + 1}
        (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).obj RY)
      (gammaV : RY ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ vMap).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj RZ)
      (gammaUV : RX ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫
        uMap)).sheafPushforwardContinuous CommRingCat.{u + 1}
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj RZ),
    (∀ (W : X.Etaleᵒᵖ) (r : R),
      gammaU.hom.app W (etaX.app W r) =
        etaY.app ((MorphismProperty.Over.pullback @Etale ⊤ uMap).op.obj W) r) →
    (∀ (W : Y.Etaleᵒᵖ) (r : R),
      gammaV.hom.app W (etaY.app W r) =
        etaZ.app ((MorphismProperty.Over.pullback @Etale ⊤ vMap).op.obj W) r) →
    (∀ (W : X.Etaleᵒᵖ) (r : R),
      gammaUV.hom.app W (etaX.app W r) =
        etaZ.app ((MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫ uMap)).op.obj W) r) →
    (fun (UX : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX) ⥤ Sheaf (X.smallGrothendieckTopology @Etale)
      AddCommGrpCat.{u + 1})
      (UY : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤ Sheaf (Y.smallGrothendieckTopology @Etale)
        AddCommGrpCat.{u + 1})
      (UZ : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ) ⥤ Sheaf (Z.smallGrothendieckTopology @Etale)
        AddCommGrpCat.{u + 1})
      (PU : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤ SheafOfModules.{u + 1} ((sheafCompose
        (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX))
      (PV : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ) ⥤ SheafOfModules.{u + 1} ((sheafCompose
        (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
      (PUV : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ) ⥤ SheafOfModules.{u + 1} ((sheafCompose
        (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX))
      (pU : PU ⋙ UX ≅ UY ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} uMap)
      (pV : PV ⋙ UY ≅ UZ ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} vMap)
      (pUV : PUV ⋙ UX ≅ UZ ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} (vMap ≫ uMap)) =>
    ∀ (LU : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX) ⥤ SheafOfModules.{u + 1} ((sheafCompose
      (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
      (eU : LU ⋙ UY ≅ UX ⋙ Etale.upperStar AddCommGrpCat.{u + 1} uMap)
      (aU : LU ⊣ PU),
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) (F : SheafOfModules.{u + 1} ((sheafCompose
      (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
      (h : LU.obj G ⟶ F),
      UX.map (aU.homEquiv G F h) ≫ pU.hom.app F =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} uMap).homEquiv
          (UX.obj G) (UY.obj F) (eU.inv.app G ≫ UY.map h)) →
    ∀ (LV : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤ SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (eV : LV ⋙ UZ ≅ UY ⋙ Etale.upperStar AddCommGrpCat.{u + 1} vMap)
      (aV : LV ⊣ PV),
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)) (F : SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (h : LV.obj G ⟶ F),
      UY.map (aV.homEquiv G F h) ≫ pV.hom.app F =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} vMap).homEquiv
          (UY.obj G) (UZ.obj F) (eV.inv.app G ≫ UZ.map h)) →
    ∀ (LUV : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX) ⥤ SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (eUV : LUV ⋙ UZ ≅ UX ⋙ Etale.upperStar AddCommGrpCat.{u + 1} (vMap ≫ uMap))
      (aUV : LUV ⊣ PUV),
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) (F : SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (h : LUV.obj G ⟶ F),
      UX.map (aUV.homEquiv G F h) ≫ pUV.hom.app F =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (vMap ≫ uMap)).homEquiv
          (UX.obj G) (UZ.obj F) (eUV.inv.app G ≫ UZ.map h)) →
    ∃ (d : PUV ≅ PV ⋙ PU) (c : LU ⋙ LV ≅ LUV),
      (∀ F : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ),
        UX.map (d.hom.app F) ≫ pU.hom.app (PV.obj F) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} uMap).map (pV.hom.app F) =
          pUV.hom.app F ≫
          (Etale.lowerStarComp AddCommGrpCat.{u + 1} vMap uMap).inv.app (UZ.obj F)) ∧
      (∀ G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RX),
        UZ.map (c.hom.app G) ≫ eUV.hom.app G =
          eV.hom.app (LU.obj G) ≫
            (Etale.upperStar AddCommGrpCat.{u + 1} vMap).map (eU.hom.app G) ≫
            (Etale.upperStarComp AddCommGrpCat.{u + 1} vMap uMap).inv.app (UX.obj G)) ∧
      (∀ G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RX),
        (aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c.hom.app G) =
          aUV.unit.app G ≫ d.hom.app (LUV.obj G)) ∧
      (∀ c' : LU ⋙ LV ≅ LUV,
        (∀ G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
          CommRingCat.{u + 1} RingCat.{u + 1})).obj RX),
          (aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c'.hom.app G) =
            aUV.unit.app G ≫ d.hom.app (LUV.obj G)) → c' = c))
      (SheafOfModules.toSheaf ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) (SheafOfModules.toSheaf ((sheafCompose
        (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
        (SheafOfModules.toSheaf ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (SheafOfModules.pushforward (J := (X.smallGrothendieckTopology @Etale)) (K :=
        (Y.smallGrothendieckTopology @Etale))
        (F := MorphismProperty.Over.pullback @Etale ⊤ uMap)
        ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u
          + 1})).map (Y := ((MorphismProperty.Over.pullback @Etale ⊤
          uMap).sheafPushforwardContinuous CommRingCat.{u + 1} (X.smallGrothendieckTopology @Etale)
          (Y.smallGrothendieckTopology @Etale)).obj RY) gammaU))
      (SheafOfModules.pushforward (J := (Y.smallGrothendieckTopology @Etale)) (K :=
        (Z.smallGrothendieckTopology @Etale))
        (F := MorphismProperty.Over.pullback @Etale ⊤ vMap)
        ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u
          + 1})).map (Y := ((MorphismProperty.Over.pullback @Etale ⊤
          vMap).sheafPushforwardContinuous CommRingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale)).obj RZ) gammaV))
      (SheafOfModules.pushforward (J := (X.smallGrothendieckTopology @Etale)) (K :=
        (Z.smallGrothendieckTopology @Etale))
        (F := MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫ uMap))
        ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u
          + 1})).map (Y := ((MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫
          uMap)).sheafPushforwardContinuous CommRingCat.{u + 1} (X.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale)).obj RZ) gammaUV))
      (Iso.refl _) (Iso.refl _) (Iso.refl _))
      ((constantSheaf (X.smallGrothendieckTopology @Etale) CommRingCat.{u + 1}).obj R)
      ((constantSheaf (Y.smallGrothendieckTopology @Etale) CommRingCat.{u + 1}).obj R)
      ((constantSheaf (Z.smallGrothendieckTopology @Etale) CommRingCat.{u + 1}).obj R)
      (toSheafify (X.smallGrothendieckTopology @Etale) ((Functor.const X.Etaleᵒᵖ).obj R))
      (toSheafify (Y.smallGrothendieckTopology @Etale) ((Functor.const Y.Etaleᵒᵖ).obj R))
      (toSheafify (Z.smallGrothendieckTopology @Etale) ((Functor.const Z.Etaleᵒᵖ).obj R))
 := by
  intros gammaU gammaV gammaUV hU hV hUV LU eU aU hLU LV eV aV hLV LUV eUV aUV hLUV
  exact exists_comparison_with_unique_unit (aU.comp aV) aUV _ _
    (etaleInverseImageCompositionModuleLinearCore X Y Z uMap vMap R
      gammaU gammaV gammaUV hU hV hUV LU eU aU hLU LV eV aV hLV LUV eUV aUV hLUV)

end AlgebraicGeometry
