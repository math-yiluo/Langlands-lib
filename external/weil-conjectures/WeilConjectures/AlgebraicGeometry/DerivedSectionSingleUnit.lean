/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-! # The section pullback and the right-derived unit on singles

Source: Stacks Project, Tag 07A6 and the defining composite unit of the Leray comparison.
(blueprint: lem-sbc-derived-section-single-unit).
-/

@[expose] public section


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

private theorem single_factor {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (M : C) :
    (L.mapDerivedCategorySingleFunctor 0).hom.app M =
      L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj M) ≫
        DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app M) := by
  rw [← cancel_epi (L.mapDerivedCategoryFactors.inv.app
    ((CochainComplex.singleFunctor C 0).obj M))]
  simpa only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc] using
    L.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M

private theorem single_chain_map {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ E) (L : C ⥤ D) (R : D ⥤ E) [F.Additive] [L.Additive] [R.Additive]
    (M : C)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M) ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)))
    (s : F.obj M ⟶ R.obj (L.obj M)) (h : v.f 0 = s) :
    (F.mapCochainComplexSingleFunctor 0).inv.app M ≫ v ≫
      (R.mapHomologicalComplex (.up ℤ)).map ((L.mapCochainComplexSingleFunctor 0).hom.app M) =
    (CochainComplex.singleFunctor E 0).map s ≫
      (R.mapCochainComplexSingleFunctor 0).inv.app (L.obj M) := by
  apply HomologicalComplex.from_single_hom_ext
  dsimp [Functor.mapCochainComplexSingleFunctor]
  simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simpa [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single]
    using h


-- The Leray comparison carries the composite derived unit to the unit on Y.
private lemma leray_fac {X Y : Scheme.{v}} (f : Y ⟶ X) :
    Functor.rightDerivedFunctorCompUnit
        (lowerStar AddCommGrpCat.{v + 1} f)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} f).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f).hom (.up ℤ))
        DerivedCategory.Qh ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit := by
  let F := lowerStar AddCommGrpCat.{v + 1} f
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
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
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (.up ℤ)) _

-- Compute before inverting any units, so no K-injectivity is needed here.
private lemma unit_leray_h {X Y : Scheme.{v}} (f : Y ⟶ X)
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
      (.up ℤ)) :
    let L := upperStar AddCommGrpCat.{v + 1} f
    let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
    let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
    let a := upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f
    let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f
    G.rightDerivedFunctorUnit.app K ≫
        G.rightDerivedFunctor.map
          (a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj K)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} f).hom.app
            (L.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
        H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (.up ℤ)).map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
            ((L.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) := by
  dsimp only
  let L := upperStar AddCommGrpCat.{v + 1} f
  let F := lowerStar AddCommGrpCat.{v + 1} f
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
  let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
  let a := upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f
  let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f
  let T := (L.mapHomotopyCategory (.up ℤ)).obj K
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    F.rightDerivedFunctorUnit K
  have hn := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    AddCommGrpCat.{v + 1} f).hom.naturality (L.mapDerivedCategoryFactorsh.hom.app K)
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
        AddCommGrpCat.{v + 1} f).hom.app (DerivedCategory.Qh.obj T) = _ at hc
  rw [hi, DerivedCategory.Qh.map_id, Category.id_comp] at hc
  erw [← hn]
  erw [← Functor.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hg, hc, ← DerivedCategory.Qh.map_comp_assoc]

private lemma sections_unit {X Y : Scheme.{v}} (f : Y ⟶ X)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app M) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f).hom.app
        ((upperStar AddCommGrpCat.{v + 1} f).obj M) =
      globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f M := by
  dsimp only [lowerStarCompGlobalSectionsIso, Functor.isoWhiskerLeft_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [← Category.assoc, (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    AddCommGrpCat.{v + 1} terminalIsTerminal).hom.naturality
      ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app M)]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Before taking homology, the unit–Leray pullback intertwines the two
right-derived units on single sheaves.
Source: Stacks Project, Tag 07A6 (derived adjunction), and the defining
right-derived composite unit for Leray.
(blueprint: lem-sbc-derived-section-single-unit).

Proof: Apply the defining equation for the derived adjunction unit to the
homotopy-category image of M[0]. Apply Γ to that equation, then use naturality
of the Γ right-derived unit. The defining equation of rightDerivedFunctorCompIso'
identifies the composite right-derived unit with the unit of Γ on the source
scheme. The remaining underived composite is Γ of the adjunction unit followed
by Γ f_* ≅ Γ, which is ordinary section pullback. Move the exact inverse-image
single comparison through the result. The mapCochainComplexSingleFunctor and
singleFunctorIsoCompQ comparisons identify all complexes with their singles;
their naturality turns the sectionwise map into singleFunctor.map of ordinary
section pullback. Reassociate and cancel the inverse comparison pairs. Neither
unit nor section pullback is inverted, so no injectivity of M or of f^*M is needed,
and the argument applies to empty schemes. -/
theorem derivedSectionPullback_single_unit {Y X : Scheme.{v}} (f : X ⟶ Y)
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (let τ : rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y ⟶
        D(upperStar AddCommGrpCat.{v + 1} f) ⋙
          rightDerivedGlobalSections AddCommGrpCat.{v + 1} X :=
      Functor.whiskerRight
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y) ≫
      Functor.whiskerLeft D(upperStar AddCommGrpCat.{v + 1} f)
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{v + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{v + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal).symm)).hom
    let Q := upperStar AddCommGrpCat.{v + 1} f
    let F := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}
    let R := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
    F.rightDerivedSingleUnit M ≫
      τ.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      R.rightDerivedFunctor.map ((Q.mapDerivedCategorySingleFunctor 0).hom.app M) =
    (DerivedCategory.singleFunctor AddCommGrpCat.{v + 1} 0).map
        (globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f M) ≫
      R.rightDerivedSingleUnit (Q.obj M))  := by
  extract_lets τ L F R
  let I := (CochainComplex.singleFunctor _ 0).obj M
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  have hfactor : L.mapDerivedCategoryFactorsh.hom.app K =
      L.mapDerivedCategoryFactors.hom.app I := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.comp_id]
    repeat erw [Category.id_comp]
  have h := unit_leray_h f K
  dsimp only at h
  rw [hfactor] at h
  dsimp only [Functor.rightDerivedSingleUnit]
  have hs := single_factor L M
  rw [hs, Functor.map_comp]
  simp only [Category.assoc]
  have hh := congrArg (fun t ↦
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫ t ≫
      R.rightDerivedFunctor.map
        (DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app M))) h
  simp only [Category.assoc] at hh
  dsimp only [τ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  refine hh.trans ?_
  let j := (L.mapCochainComplexSingleFunctor 0).hom.app M
  let a := upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f
  let e := lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} f
  let v := (F.mapHomologicalComplex (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
      ((L.mapHomologicalComplex (.up ℤ)).obj I)
  have hv : DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map
          ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
          ((L.mapHomotopyCategory (.up ℤ)).obj K)) = DerivedCategory.Q.map v := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rfl
  have hn := R.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map j)
  dsimp only [Functor.comp_map] at hn
  erw [hv, ← hn]
  change DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫
      DerivedCategory.Q.map v ≫
        DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map j) ≫
          R.rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              ((CochainComplex.singleFunctor _ 0).obj (L.obj M))) =
    (DerivedCategory.singleFunctor AddCommGrpCat.{v + 1} 0).map
        (globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f M) ≫
      DerivedCategory.Q.map ((R.mapCochainComplexSingleFunctor 0).inv.app (L.obj M)) ≫ _
  have hc : (F.mapCochainComplexSingleFunctor 0).inv.app M ≫ v ≫
      (R.mapHomologicalComplex (.up ℤ)).map j =
    (CochainComplex.singleFunctor AddCommGrpCat.{v + 1} 0).map
        (globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f M) ≫
      (R.mapCochainComplexSingleFunctor 0).inv.app (L.obj M) := by
    exact single_chain_map F L R M v
      (globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f M) (sections_unit f M)
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc, Category.assoc, hc,
    DerivedCategory.Q.map_comp, Category.assoc]
  rfl


end AlgebraicGeometry.Etale.RawRestrictedComparison
