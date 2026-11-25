/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
public import WeilConjectures.CategoryTheory.CanonicalResolutionDerivedIso
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.CanonicalResolutionHomologyComparison
import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Resolution comparisons and the composite derived unit

Source: Stacks Project, derived.tex, Tags 015M and 015N.
(blueprint: lem-pc-grothendieck-resolution-unit-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private lemma resolutionDerivedIso_comp
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

set_option backward.isDefEq.respectTransparency false in
private lemma mapExtendIso_comp_hom
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

set_option backward.isDefEq.respectTransparency false in
private lemma canonicalResolutionDerivedIso_comp
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
theorem resolution_composite_unit_transport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{vA} A] {B : Type uB} [Category.{vB} B]
    [Abelian B] [IsGrothendieckAbelian.{vB} B] {C : Type uC} [Category.{vC} C]
    [Abelian C] [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory A]
    [HasDerivedCategory B] [HasDerivedCategory C] (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
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
          (G.rightDerivedFunctorPlusUnit.app
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩) := by
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
  congr 3
  erw [Functor.rightDerivedFunctorPlusUnit_app]
  change _ = (𝟙 _) ≫ DerivedCategory.Plus.Qh.map (𝟙 _) ≫ _ ≫
    G.rightDerivedFunctorPlus.map (𝟙 _)
  erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]

end CategoryTheory
