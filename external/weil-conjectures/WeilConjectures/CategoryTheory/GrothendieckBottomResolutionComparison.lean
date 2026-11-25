/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.CanonicalResolutionHomologyComparison
import WeilConjectures.CategoryTheory.GrothendieckBottomAugmentation

/-! # The Grothendieck bottom edge on resolution comparisons

Source: Stacks Project, Tags 015M, 015N and 015J.
(blueprint: lem-sc-grothendieck-bottom-resolution-comparison)
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Homology of the canonical resolution comparison transports the composite derived unit.
Source: Stacks Project, Tags 015M and 015N, composition unit and abutment identification.
(blueprint: lem-pc-canonical-resolution-composite-unit-comparison).

Proof: Expand grothendieckSpectralObjectHBotTopIso as the inverse composition comparison
followed by the single-object homology comparison. Apply the ordinary canonical
resolution homology identity to F composed with G and cancel its resolution comparison.
The resulting map is homology of the composition comparison followed by RG applied to
the canonical F comparison. Before applying homology, the defining unit equation for
the composition comparison and its naturality along the resolution augmentation give
resolutionDerivedIso_comp above: invert the GF unit and cancel the F unit on the complex
of injectives. Naturality of the G unit along the F map/extension comparison moves that
comparison to its source. The map/extension comparison for GF equals the composite of
G applied to the F comparison and the G comparison; this equality holds degreewise
from the definitions, including the zero terms in negative degrees. Apply homology and
naturality of homologyFunctorObjQIso, then cancel the extension homology comparisons.
The remaining factors are exactly the inverse G map/extension comparison and the G unit
shown on the right. No positive-degree condition is used.
-/
private lemma bottom_resolution_composite_unit_transport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{vA} A] {B : Type uB} [Category.{vB} B]
    [Abelian B] [IsGrothendieckAbelian.{vB} B] {C : Type uC} [Category.{vC} C]
    [Abelian C] [HasDerivedCategory A]
    [HasDerivedCategory B] [HasDerivedCategory C] (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G)
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
      (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
          (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
          (DerivedCategory.Plus.homologyFunctor C n).map
            (G.rightDerivedFunctorPlus.map (canonicalResolutionDerivedIso F I).hom) =
        (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).inv ≫
        HomologicalComplex.homologyMap
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).mapExtendIso
            ComplexShape.embeddingUpNat G).inv (n : ℤ) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          (G.mapCochainComplexPlus.obj
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient B).obj
              ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
                ComplexShape.embeddingUpNat, 0, inferInstance⟩)) := by
  have resolutionDerivedIso_comp
      {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
      {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
      {C : Type uC} [Category.{vC} C] [Abelian C]
      [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
      (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
      (hFG : ∀ (J : A) [Injective J], G.rightAcyclic (F.obj J))
      {X : A} (I : InjectiveResolution X) :
      (F.rightDerivedFunctorPlusCompIsoOfRightAcyclic G hFG).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
          G.rightDerivedFunctorPlus.map (resolutionDerivedIso F I).hom =
        (resolutionDerivedIso (F ⋙ G) I).hom ≫
          G.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient B).obj
              ⟨(F.mapHomologicalComplex _).obj I.cochainComplex, 0, inferInstance⟩) := by
    let L : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
    let H := (HomotopyCategory.Plus.quotient A).obj L
    have : ∀ n, Injective (L.obj.X n) := fun n ↦
      inferInstanceAs (Injective (I.cochainComplex.X n))
    let c := F.rightDerivedFunctorPlusCompIsoOfRightAcyclic G hFG
    have hc : (F ⋙ G).rightDerivedFunctorPlusUnith.app H ≫
        c.hom.app (DerivedCategory.Plus.Qh.obj H) =
          G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj H) ≫
            G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app H) := by
      dsimp [c, Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic]
      have := F.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_of_rightAcyclic G hFG
      simp only [Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
        Functor.rightDerivedNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
      exact Functor.rightDerivedFunctorPlusCompUnit_app F G H
    have hn := c.hom.naturality (resolutionAugmentationIso I).hom
    dsimp [resolutionDerivedIso]
    simp only [Functor.map_comp]
    dsimp only [Functor.comp_map] at hn
    erw [← Category.assoc, ← hn, Category.assoc]
    simp only [Category.assoc]
    congr 1
    apply (cancel_epi ((F ⋙ G).rightDerivedFunctorPlusUnith.app H)).1
    erw [← Category.assoc, hc]
    have hA : (DerivedCategory.Plus.quotientCompQhIso A).inv.app L = 𝟙 _ := rfl
    have hB : (DerivedCategory.Plus.quotientCompQhIso B).hom.app
        (F.mapCochainComplexPlus.obj L) = 𝟙 _ := rfl
    have hC : (DerivedCategory.Plus.quotientCompQhIso C).hom.app
        ((F ⋙ G).mapCochainComplexPlus.obj L) = 𝟙 _ := rfl
    erw [hA, hB, hC]
    simp only [Functor.comp_obj, Functor.map_id, Functor.map_inv, Category.id_comp, Category.assoc,
      IsIso.hom_inv_id_assoc, H, L]
    erw [Functor.map_id, Category.comp_id, Category.id_comp]
    rfl
  have mapExtendIso_comp_hom
      {A : Type uA} [Category.{vA} A] [Abelian A]
      {B : Type uB} [Category.{vB} B] [Abelian B]
      {C : Type uC} [Category.{vC} C] [Abelian C]
      (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
      (K : CochainComplex A ℕ) :
      (K.mapExtendIso ComplexShape.embeddingUpNat (F ⋙ G)).hom =
        (G.mapHomologicalComplex _).map
            (K.mapExtendIso ComplexShape.embeddingUpNat F).hom ≫
          (((F.mapHomologicalComplex _).obj K).mapExtendIso
            ComplexShape.embeddingUpNat G).hom := by
    ext i
    by_cases hi : ∃ j, ComplexShape.embeddingUpNat.f j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
      dsimp [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents]
      rw [HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f j),
        HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f j),
        HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f j)]
      simp [eqToHom_map]
    · apply IsZero.eq_of_tgt
      exact HomologicalComplex.isZero_extend_X _ _ _ (by simpa using hi)
  have canonicalResolutionDerivedIso_comp
      {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
      {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
      {C : Type uC} [Category.{vC} C] [Abelian C]
      [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
      (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
      (hFG : ∀ (J : A) [Injective J], G.rightAcyclic (F.obj J))
      {X : A} (I : InjectiveResolution X) :
      (F.rightDerivedFunctorPlusCompIsoOfRightAcyclic G hFG).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
          G.rightDerivedFunctorPlus.map (canonicalResolutionDerivedIso F I).hom =
        (canonicalResolutionDerivedIso (F ⋙ G) I).hom ≫
          DerivedCategory.Plus.Q.map
            ((CochainComplex.plus C).isoMk
              (X := G.mapCochainComplexPlus.obj
                ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
                  ComplexShape.embeddingUpNat, 0, inferInstance⟩)
              (Y := ⟨(((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
                I.cocomplex).extend ComplexShape.embeddingUpNat, 0, inferInstance⟩)
              (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).mapExtendIso
                ComplexShape.embeddingUpNat G)).inv ≫
          G.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient B).obj
              ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
                ComplexShape.embeddingUpNat, 0, inferInstance⟩) := by
    let mF : F.mapCochainComplexPlus.obj ⟨I.cochainComplex, 0, inferInstance⟩ ≅
        ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
          ComplexShape.embeddingUpNat, 0, inferInstance⟩ :=
      (CochainComplex.plus B).isoMk
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)
    let mG : G.mapCochainComplexPlus.obj
        (⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
          ComplexShape.embeddingUpNat, 0, inferInstance⟩) ≅
        ⟨(((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
          ComplexShape.embeddingUpNat, 0, inferInstance⟩ := (CochainComplex.plus C).isoMk
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).mapExtendIso
        ComplexShape.embeddingUpNat G)
    let mFG : (F ⋙ G).mapCochainComplexPlus.obj ⟨I.cochainComplex, 0, inferInstance⟩ ≅
        ⟨(((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
          ComplexShape.embeddingUpNat, 0, inferInstance⟩ := (CochainComplex.plus C).isoMk
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (F ⋙ G))
    have hm : mFG.hom = G.mapCochainComplexPlus.map mF.hom ≫ mG.hom := by
      apply ObjectProperty.hom_ext
      exact mapExtendIso_comp_hom F G I.cocomplex
    have hn := G.rightDerivedFunctorPlusUnith.naturality
      ((HomotopyCategory.Plus.quotient B).map mF.hom)
    dsimp [canonicalResolutionDerivedIso]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, resolutionDerivedIso_comp F G hFG I, Category.assoc]
    change (resolutionDerivedIso (F ⋙ G) I).hom ≫
        G.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient B).obj
            (F.mapCochainComplexPlus.obj ⟨I.cochainComplex, 0, inferInstance⟩)) ≫
          G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map mF.hom) =
      (resolutionDerivedIso (F ⋙ G) I).hom ≫ DerivedCategory.Plus.Q.map mFG.hom ≫
        DerivedCategory.Plus.Q.map mG.inv ≫ G.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient B).obj
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩)
    rw [hm]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (DerivedCategory.Plus.Q.map mG.hom),
      ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    congr 1
    exact hn.symm
  let mG : G.mapCochainComplexPlus.obj
      ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat, 0, inferInstance⟩ ≅
      ⟨(((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat, 0, inferInstance⟩ := (CochainComplex.plus C).isoMk
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).mapExtendIso
      ComplexShape.embeddingUpNat G)
  have hn := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality mG.inv n
  have hc := canonicalResolutionDerivedIso_comp F G
    (fun J _ q ↦ hFG J (q + 1) (by lia)) I
  have hh := resolution_homology_transport (F ⋙ G) X I n
  apply (cancel_epi (I.isoRightDerivedObj (F ⋙ G) n).hom).1
  apply (cancel_epi
    ((F ⋙ G).homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    ((F ⋙ G).homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom
    (I.isoRightDerivedObj (F ⋙ G) n).hom, hh]
  simp only [Category.assoc]
  dsimp [Functor.grothendieckSpectralObjectHBotTopIso,
    Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, hc]
  simp only [Functor.map_comp]
  erw [Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    (DerivedCategory.Plus.homologyFunctorObjQIso _ n).hom]
  erw [← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl



set_option backward.isDefEq.respectTransparency false in
private lemma bottom_resolution_map_unit
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] (Y : B) (J : InjectiveResolution Y)
    (K : CochainComplex B ℕ) (φ : J.cocomplex ⟶ K) (n : ℕ) :
    let L : CochainComplex.Plus B :=
      ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
    let f : (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus B) ⟶ L :=
      ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
    (J.isoRightDerivedObj G n).hom ≫
        HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℕ)).map φ) n ≫
        (((G.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).inv ≫
        HomologicalComplex.homologyMap (K.mapExtendIso ComplexShape.embeddingUpNat G).inv n ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso (G.mapCochainComplexPlus.obj L) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj L)) =
      (G.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (resolutionAugmentationIso J).hom) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
  dsimp only
  let L : CochainComplex.Plus B :=
    ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let LJ : CochainComplex.Plus B := ⟨J.cochainComplex, 0, inferInstance⟩
  let f : LJ ⟶ L :=
    ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  let mJ := J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G
  let mK := K.mapExtendIso ComplexShape.embeddingUpNat G
  have he := HomologicalComplex.extendHomologyIso_hom_naturality
    ((G.mapHomologicalComplex (.up ℕ)).map φ) ComplexShape.embeddingUpNat
    (rfl : (n : ℤ) = n)
  have hq := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (G.mapCochainComplexPlus.map f) (n : ℤ)
  have hu := G.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.quotient B).map f)
  have hh := resolution_homology_transport G Y J n
  apply (cancel_epi (G.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y n).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hh]
  simp only [Category.assoc]
  rw [← reassoc_of% he]
  simp only [Iso.hom_inv_id_assoc]
  simp only [canonicalResolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have hqJ := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    ((CochainComplex.plus C).isoMk
      (X := G.mapCochainComplexPlus.obj LJ)
      (Y := ⟨((G.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).extend
        ComplexShape.embeddingUpNat, 0, inferInstance⟩) mJ).hom (n : ℤ)
  rw [reassoc_of% hqJ]
  have hm' :
      mJ.hom ≫ HomologicalComplex.extendMap
          ((G.mapHomologicalComplex (.up ℕ)).map φ) ComplexShape.embeddingUpNat ≫ mK.inv =
        (G.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) := by
    apply (cancel_mono mK.hom).1
    have hm₀ :
        (G.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) ≫ mK.hom =
          mJ.hom ≫ HomologicalComplex.extendMap
            ((G.mapHomologicalComplex (.up ℕ)).map φ) ComplexShape.embeddingUpNat := by
      ext i
      exact HomologicalComplex.mapExtensIso_hom_f_naturality φ
        ComplexShape.embeddingUpNat G i
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hm₀.symm
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc]
  simp only [Category.assoc]
  erw [hm']
  erw [← reassoc_of% hq, Iso.hom_inv_id_assoc]
  have hu' : DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map f) ≫
        G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj L) =
      G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj LJ) ≫
        G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) := hu
  have hhu := congrArg ((DerivedCategory.Plus.homologyFunctor C n).map) hu'
  simp only [Functor.map_comp] at hhu
  erw [hhu]
  dsimp only [resolutionDerivedIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, asIso_inv,
    Functor.map_comp, Category.assoc]
  have hB : (DerivedCategory.Plus.quotientCompQhIso B).inv.app LJ = 𝟙 _ := rfl
  have hC : (DerivedCategory.Plus.quotientCompQhIso C).hom.app
      (G.mapCochainComplexPlus.obj LJ) = 𝟙 _ := rfl
  erw [hB, hC]
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp]
  have : ∀ i, Injective (LJ.obj.X i) := fun i ↦
    inferInstanceAs (Injective (J.cochainComplex.X i))
  erw [← Functor.map_comp_assoc (DerivedCategory.Plus.homologyFunctor C n)
    (inv (G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj LJ)))]
  erw [IsIso.inv_hom_id, Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The bottom edge is computed by applying the second functor to a comparison
from a resolution of `F(X)` to `F(I)`.

Source: Stacks Project, Tags 015M, 015N and 015J, the degree-zero augmentation.
(blueprint: lem-sc-grothendieck-bottom-resolution-comparison)

Proof: Extend both complexes by zero to the bounded below homotopy category.
The augmentation of J identifies J with F(X) in the derived category. The supplied
comparison represents the canonical map F(X)[0] to RF(X): its degree-zero
augmentation identity identifies it with the derived unit. Indeed, after
precomposition with the quasi-isomorphism F(X)[0] to J, the maps agree as
complex maps; cancelling that isomorphism in the derived category proves
independence of the comparison. Under the truncation comparison for H^0(RF(X)), this is
exactly the map from the bottom interval into the full interval. Apply RG and
homology. The G unit on J is invertible since J has injective terms; the G unit
on F(I) is invertible by hFG. Naturality of that unit makes the resulting map
homology of G(phi). The canonical resolution computations identify its endpoints
with R^n G(F(X)) and R^n(GF)(X). Their order is the displayed hom/inv order.
This works also for n=0, with no incoming differential and no shift sign.
-/
theorem grothendieckBottomEdgeMap_eq_resolution
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) (I : InjectiveResolution X)
    (J : InjectiveResolution (F.obj X))
    (φ : J.cocomplex ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = F.map (I.ι.f 0)) (n : ℕ) :
    (F.grothendieckBottomEdgeMap G hFG n).app X =
      (J.isoRightDerivedObj G n).hom ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
        (I.isoRightDerivedObj (F ⋙ G) n).inv := by
  have ha := grothendieckBottomEdge_augmentation F G X I J φ hφ n
  have hu := bottom_resolution_map_unit G (F.obj X) J
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) φ n
  have hc := bottom_resolution_composite_unit_transport F G hFG X I n
  apply (cancel_mono
    ((F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        (G.rightDerivedFunctorPlus.map (canonicalResolutionDerivedIso F I).hom))).1
  simp only [Functor.grothendieckBottomEdgeMap, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hc]
  exact ha.trans hu.symm

end CategoryTheory
