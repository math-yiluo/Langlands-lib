/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Unit--Leray computation on K-injective complexes

Source: Stacks Project, Tags 08BJ, 070I, 01F8, 01F9, 01FA and 08J6.
(blueprint: lem-weil-pbc-kinjective-unit-leray).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- The Leray comparison carries the composite derived unit to the unit on Y.
private lemma leray_fac {X Y : Scheme.{uNatural}} (f : Y ⟶ X) :
    Functor.rightDerivedFunctorCompUnit
        (lowerStar AddCommGrpCat.{uNatural + 1} f)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{uNatural + 1} f).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{uNatural + 1} f).hom (.up ℤ))
        DerivedCategory.Qh ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).rightDerivedFunctorUnit := by
  let F := lowerStar AddCommGrpCat.{uNatural + 1} f
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  have hcomp : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hcomp, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedLowerStarCompRightDerivedGlobalSectionsIso,
    Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
  dsimp only [F, G]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) (.up ℤ)) _

-- Compute before inverting any units, so no K-injectivity is needed here.
private lemma unit_leray_h {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
      (.up ℤ)) :
    let L := upperStar AddCommGrpCat.{uNatural + 1} f
    let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
    let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
    let a := upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f
    let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{uNatural + 1} f
    G.rightDerivedFunctorUnit.app K ≫
        G.rightDerivedFunctor.map
          (a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj K)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{uNatural + 1} f).hom.app
            (L.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
        H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (.up ℤ)).map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
            ((L.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) := by
  dsimp only
  let L := upperStar AddCommGrpCat.{uNatural + 1} f
  let F := lowerStar AddCommGrpCat.{uNatural + 1} f
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let a := upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f
  let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{uNatural + 1} f
  let T := (L.mapHomotopyCategory (.up ℤ)).obj K
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    F.rightDerivedFunctorUnit K
  have hn := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    AddCommGrpCat.{uNatural + 1} f).hom.naturality (L.mapDerivedCategoryFactorsh.hom.app K)
  have hg := G.rightDerivedFunctorUnit.naturality
    ((a.mapHomotopyCategory (.up ℤ)).unit.app K)
  have hc := NatTrans.congr_app (leray_fac f) T
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  dsimp only [Functor.comp_map] at hn hg
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  change DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T) ≫
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{uNatural + 1} f).hom.app (DerivedCategory.Qh.obj T) = _ at hc
  rw [hi, DerivedCategory.Qh.map_id, Category.id_comp] at hc
  erw [← hn]
  erw [← Functor.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hg, hc, ← DerivedCategory.Qh.map_comp_assoc]

private lemma sections_unit {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app M) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{uNatural + 1} f).hom.app
        ((upperStar AddCommGrpCat.{uNatural + 1} f).obj M) =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f M := by
  dsimp only [lowerStarCompGlobalSectionsIso, Functor.isoWhiskerLeft_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [← Category.assoc, (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    AddCommGrpCat.{uNatural + 1} terminalIsTerminal).hom.naturality
      ((upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app M)]
  rfl

/-- The unit--Leray map on K-injective complexes is represented by the sectionwise map.
Source: Stacks Project, Tags 08BJ and 070I; cohomology.tex, Tags 01F8--01FA;
sites-cohomology.tex, Tag 08J6.
(blueprint: lem-weil-pbc-kinjective-unit-leray).

Proof: Adjoint j to a map I → f_*J. Since inverse image is exact, direct image
preserves K-injectives (Tag 08BJ). The derived units on I, J and f_*J are therefore
invertible. Expand the derived adjunction unit using its defining unit compatibility.
Move the factorization isomorphism for exact inverse image through the Leray
isomorphism by naturality. The composite right-derived unit compatibility for
f_* followed by Γ identifies the remaining factors with Γ of the underived
adjunction unit followed by the sectionwise identification Γ_X f_* ≅ Γ_Y.
Naturality of the Γ_Y unit with respect to j gives the last factor Γ_Y(j).
In degree i the resulting chain map is globalSectionsUpperStarMap applied to I.X i
followed by Γ_Y(j.f i), hence it is w by extensionality. Localizing gives the
asserted equality, with the inverse units expressed as rightDerivedFunctorObjQIso.
No resolution augmentation or homology functor is used in this calculation. -/
theorem etaleKInjective_unit_leray
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    (J : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶
        ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)
    (hw : ∀ i : ℤ, w.f i =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (I.X i) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (j.f i)) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).rightDerivedFunctorObjQIso
        I).hom ≫ DerivedCategory.Q.map w ≫
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).rightDerivedFunctorObjQIso
        J).inv =
      (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
            (DerivedCategory.Q.obj I)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{uNatural + 1} f).hom.app
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
              (DerivedCategory.Q.obj I)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
          ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app I ≫
            DerivedCategory.Q.map j) := by
  let L := upperStar AddCommGrpCat.{uNatural + 1} f
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let a := upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f
  let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{uNatural + 1} f
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let U := (L.mapHomotopyCategory (.up ℤ)).obj K
  let v := (G.mapHomologicalComplex (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
      ((L.mapHomologicalComplex (.up ℤ)).obj I)
  have hw' : w = v ≫ (H.mapHomologicalComplex (.up ℤ)).map j := by
    ext i : 1
    change w.f i = (G.map (a.unit.app (I.X i)) ≫
      e.hom.app (L.obj (I.X i))) ≫ H.map (j.f i)
    rw [sections_unit, hw i]
  let β : G.rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
    (Functor.leftUnitor G.rightDerivedFunctor).inv ≫
      Functor.whiskerRight a.mapDerivedCategoryRightDerivedAdjunction.unit G.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L.mapDerivedCategory
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{uNatural + 1} f).hom
  have hquotient :
      ((G.mapHomotopyCategory (.up ℤ)).map
          ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app U) ≫
        (H.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ (.up ℤ)).map j) =
      (HomotopyCategory.quotient _ (.up ℤ)).map w := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    change (HomotopyCategory.quotient _ (.up ℤ)).map
      (v ≫ (H.mapHomologicalComplex (.up ℤ)).map j) = _
    rw [← hw']
  have hc := unit_leray_h f K
  dsimp only at hc
  have hj := H.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map j)
  dsimp only [Functor.comp_map] at hj
  have hc' := congrArg (fun t ↦ t ≫ H.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map j))) hc
  simp only [Category.assoc] at hc'
  erw [← hj, ← DerivedCategory.Qh.map_comp_assoc, hquotient] at hc'
  have hcomp : G.rightDerivedFunctorUnit.app K ≫ β.app (DerivedCategory.Qh.obj K) ≫
      H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map j)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map w) ≫
        H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj J) := by
    simpa only [β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
      Functor.map_comp, Category.assoc] using hc'
  -- Transport the homotopy computation along the canonical comparison with Q.
  have hfactor : L.mapDerivedCategoryFactorsh.hom.app K ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map j) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app J =
      L.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).hom.app I) ≫
        L.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map j := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    erw [DerivedCategory.Qh.map_id, Category.comp_id]
    simp only [Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality]
    erw [Iso.inv_hom_id_app_assoc]
  have hβ := β.naturality ((DerivedCategory.quotientCompQhIso _).hom.app I)
  dsimp only [Functor.comp_map] at hβ
  suffices (G.rightDerivedFunctorObjQIso I).hom ≫ DerivedCategory.Q.map w ≫
      (H.rightDerivedFunctorObjQIso J).inv =
      β.app (DerivedCategory.Q.obj I) ≫
        H.rightDerivedFunctor.map
          (L.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map j) by
    simpa only [β, G, H, L, a, rightDerivedGlobalSections,
      mapDerivedUpperStarLowerStarAdjunction, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
      Category.id_comp, Category.comp_id, Category.assoc] using this
  rw [← cancel_epi (G.rightDerivedFunctorObjQIso I).inv, Iso.inv_hom_id_assoc]
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, asIso_hom]
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app
    ((G.mapHomologicalComplex (.up ℤ)).obj I))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hβ, ← H.rightDerivedFunctor.map_comp, ← hfactor]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ H.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app J)) hcomp.symm

end AlgebraicGeometry.Etale
