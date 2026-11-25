/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-!
# Functoriality of `mapDerivedCategory`

For exact functors between abelian categories, the induced functor
`Functor.mapDerivedCategory` on derived categories is functorial:

- `CategoryTheory.Functor.mapDerivedCategoryNatIso`: an isomorphism `F ≅ G` of exact
  functors induces an isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryCompIso`: the composition isomorphism
  `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`.
- `CategoryTheory.Equivalence.mapDerivedCategory`: an equivalence of abelian categories
  induces an equivalence of derived categories.
- `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`: the commutation
  `H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` with the homology functors, with the
  bounded below variant `CategoryTheory.Functor.mapDerivedCategoryPlusHomologyFunctorIso`.
- `CategoryTheory.Functor.mapDerivedCategoryTruncLEIso`,
  `CategoryTheory.Functor.mapDerivedCategoryTruncGEIso`: `F.mapDerivedCategory` commutes with the
  truncations `τ^{≤ n}` and `τ^{≥ n}` of the canonical t-structures.
- `CategoryTheory.Functor.isZero_mapDerivedCategory_obj`: `F.mapDerivedCategory` kills every
  object whose homology objects are killed by `F`.
- `CategoryTheory.Functor.jointlyReflectIsomorphisms_mapDerivedCategory` and
  `CategoryTheory.Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory`: if a
  family of exact functors jointly reflects isomorphisms, so do the induced functors on
  derived categories.
- `CategoryTheory.Functor.isGE_mapDerivedCategory_obj`,
  `CategoryTheory.Functor.isLE_mapDerivedCategory_obj`,
  `CategoryTheory.Functor.homologyConcentratedIn_mapDerivedCategory_obj` and
  `CategoryTheory.Functor.bounded_mapDerivedCategory_obj`: `F.mapDerivedCategory` preserves
  the bounds of the canonical t-structure; if `F` is faithful, it also reflects them
  (`CategoryTheory.Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj`
  and `CategoryTheory.Functor.bounded_of_bounded_mapDerivedCategory_obj`).
- `CategoryTheory.Functor.mapDerivedCategoryPlus`: the restriction of
  `F.mapDerivedCategory` to the bounded below derived categories, with the compatibility
  isomorphism `CategoryTheory.Functor.mapDerivedCategoryPlusCompatibility` and the
  factorization `CategoryTheory.Functor.mapDerivedCategoryPlusFactorsh` through the
  localization functors from the bounded below homotopy categories.
- `CategoryTheory.Functor.mapDerivedCategoryPlusNatIso` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso`: the corresponding
  functoriality of `mapDerivedCategoryPlus`, obtained by cancelling the fully faithful
  inclusions `DerivedCategory.Plus.ι`.
- `CategoryTheory.Functor.mapDerivedCategoryCompIso_fac`,
  `CategoryTheory.Functor.mapDerivedCategoryCompIso_fach` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_fac`: the composition isomorphisms
  are characterized by their compatibility with the factorizations of the induced functors
  through the localization functors.
- `CategoryTheory.Functor.mapDerivedCategoryNatIso_fac`,
  `CategoryTheory.Functor.mapDerivedCategoryNatIso_fach` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh`: likewise, the
  isomorphism induced by `e : F ≅ G` is characterized by its compatibility with the
  factorizations; on the image of a complex it is `e` itself.
- `CategoryTheory.Functor.mapDerivedCategoryPlusSingleFunctor`: the compatibility of
  `mapDerivedCategoryPlus` with the single functors of the bounded below derived
  categories.
- `CategoryTheory.Functor.mapDerivedCategoryIdIso` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusIdIso`: the identity isomorphisms
  `(𝟭 C).mapDerivedCategory ≅ 𝟭` and `(𝟭 C).mapDerivedCategoryPlus ≅ 𝟭`, together with
  their characterizations `CategoryTheory.Functor.mapDerivedCategoryIdIso_factorsh` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusIdIso_factorsh` at the level of the
  homotopy categories.
- `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_id_comp`,
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_comp_id` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_assoc`: the unit and associativity
  laws relating `mapDerivedCategoryPlusCompIso` and `mapDerivedCategoryPlusIdIso`.
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

@[inherit_doc mapDerivedCategory]
scoped notation "D(" F ")" => mapDerivedCategory F

/-- An isomorphism `F ≅ G` of exact functors between abelian categories induces an
isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory` of the functors induced on
derived categories, compatibly with the localization functors. -/
noncomputable def mapDerivedCategoryNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The isomorphism `Functor.mapDerivedCategoryNatIso` is characterized by its
compatibility with the factorizations `Functor.mapDerivedCategoryFactors` through the
localization functors `DerivedCategory.Q`: on the image of a complex it is the levelwise
image of `e`. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_fac {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : CochainComplex C ℤ) :
    (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory = F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      G.mapDerivedCategory = G.mapDerivedCategoryFactors := rfl
  simp only [mapDerivedCategoryNatIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, hF, hG, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, isoWhiskerRight_hom, whiskerRight_app]
  rfl

/-- The homotopy category counterpart of `Functor.mapDerivedCategoryNatIso_fac`: the
isomorphism `Functor.mapDerivedCategoryNatIso` is compatible with the factorizations
`Functor.mapDerivedCategoryFactorsh` through the localization functors
`DerivedCategory.Qh`. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_fach {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hnt : (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) := rfl
  rw [mapDerivedCategoryFactorsh_hom_app, mapDerivedCategoryFactorsh_hom_app, hnt,
    ← NatTrans.naturality_assoc, mapDerivedCategoryNatIso_fac_assoc,
    reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K))]
  simp only [mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp]
  simp

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is characterized by its
compatibility with the factorizations `Functor.mapDerivedCategoryFactors` through the
localization functors `DerivedCategory.Q`. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_fac (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom.app K) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  rw [← cancel_epi ((mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K)),
    Iso.hom_inv_id_app_assoc, mapDerivedCategoryCompIso_hom_app_Q_obj]
  simp

/-- The homotopy category counterpart of `Functor.mapDerivedCategoryCompIso_fac`: the
composition isomorphism `Functor.mapDerivedCategoryCompIso` is compatible with the
factorizations `Functor.mapDerivedCategoryFactorsh` through the localization functors
`DerivedCategory.Qh` and with `Functor.mapHomotopyCategoryCompIso`. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_fach (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom.app K) =
    (F ⋙ G).mapDerivedCategoryFactorsh.hom.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hG : G.mapDerivedCategoryFactorsh.hom.app
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) =
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso D).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso E).inv.app _ ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    G.mapDerivedCategoryFactorsh_hom_app _
  have hCI : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).hom.app K) := rfl
  rw [mapDerivedCategoryFactorsh_hom_app, hG, hCI, mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Functor.map_comp,
    Category.assoc]
  simp only [comp_obj, map_id, Category.id_comp, cancelIso, Category.comp_id]
  rw [← Functor.comp_map F.mapDerivedCategory G.mapDerivedCategory,
    ← NatTrans.naturality_assoc, ← DerivedCategory.quotientCompQhIso_inv_naturality,
    mapDerivedCategoryCompIso_fac_assoc]

/-- An exact functor commutes with the homology functors of the derived categories:
the canonical isomorphism
`H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` of functors
`DerivedCategory C ⥤ D`, induced by the commutation of `F` with homology of complexes.
(blueprint: `situation-conventions`) -/
noncomputable def mapDerivedCategoryHomologyFunctorIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
      (DerivedCategory.homologyFunctor C n ⋙ F) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n) F⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
    (DerivedCategory.homologyFunctor C n ⋙ F)
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n)
    (Iso.refl _)

/-- The value of `Functor.mapDerivedCategoryHomologyFunctorIso` on the image of a cochain
complex. -/
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_Q (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (K : CochainComplex C ℤ) :
    (F.mapDerivedCategoryHomologyFunctorIso n).hom.app (DerivedCategory.Q.obj K) =
      F.map ((DerivedCategory.homologyFunctorFactors C n).hom.app K) ≫
        (F.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app K ≫
        (DerivedCategory.homologyFunctorFactors D n).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategoryFactors.inv.app K) := by
  simp [mapDerivedCategoryHomologyFunctorIso, Localization.liftNatIso,
    Localization.liftNatTrans_app]

open DerivedCategory in
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso_Q (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n a a' : ℤ) (h : n + a = a')
    (K : CochainComplex C ℤ) :
    F.map (((homologyFunctor C 0).shiftIso n a a' h).hom.app (Q.obj K)) ≫
        (F.mapDerivedCategoryHomologyFunctorIso a').hom.app (Q.obj K) =
      (F.mapDerivedCategoryHomologyFunctorIso a).hom.app ((Q.obj K)⟦n⟧) ≫
        (homologyFunctor D a).map ((F.mapDerivedCategory.commShiftIso n).hom.app (Q.obj K)) ≫
        ((homologyFunctor D 0).shiftIso n a a' h).hom.app (F.mapDerivedCategory.obj (Q.obj K)) := by
  have S₁ := shiftMap_homologyFunctor_map_Q (𝟙 (K⟦n⟧)) a a' h
  have S₂ := shiftMap_homologyFunctor_map_Q (𝟙 (((F.mapHomologicalComplex (.up ℤ)).obj K)⟦n⟧))
    a a' h
  simp only [Functor.shiftMap, ShiftedHom.map, Functor.map_id, Category.id_comp] at S₁ S₂
  have hφ := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom n K
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc] at hφ
  have hC := F.mapHomologicalComplexHomologyIso_hom_app_shiftIso n a a' h K
  have ne := (F.mapDerivedCategoryHomologyFunctorIso a).hom.naturality
    ((Q.commShiftIso n).hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at ne
  have hφ' : F.mapDerivedCategory.map ((Q.commShiftIso n).hom.app K) ≫
      (F.mapDerivedCategory.commShiftIso n).hom.app (Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app (K⟦n⟧) ≫
        Q.map (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K) ≫
        (Q.commShiftIso n).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (F.mapDerivedCategoryFactors.inv.app K)⟦n⟧' := by
    rw [← reassoc_of% hφ, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id, Category.comp_id]
  rw [← cancel_epi (F.map ((homologyFunctor C a).map ((Q.commShiftIso n).hom.app K))),
    ← F.map_comp_assoc]
  erw [S₁]
  rw [reassoc_of% ne, ← Functor.map_comp_assoc, hφ']
  have hs := (homologyFunctor D 0).shiftIso_hom_naturality n a a' h
    (F.mapDerivedCategoryFactors.inv.app K)
  simp only [Functor.map_comp, Category.assoc]
  erw [hs, reassoc_of% S₂]
  rw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
    mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  have key :
      F.map (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso n a a' h).hom.app K) ≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) a').inv.app K =
      (F.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app (K⟦n⟧) ≫
        (HomologicalComplex.homologyFunctor D (.up ℤ) a).map
          (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K) ≫
        ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso n a a' h).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
    have hc : (HomologicalComplex.homologyFunctor D (.up ℤ) a).map
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K) ≫
        (HomologicalComplex.homologyFunctor D (.up ℤ) a).map
          (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).inv.app K) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rw [← cancel_mono ((F.mapHomologicalComplexHomologyIso (.up ℤ) a').hom.app K),
      Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    simp only [Category.assoc]
    erw [← hC, reassoc_of% hc, Iso.inv_hom_id_app_assoc]
  have hF' := homologyFunctorFactors_hom_naturality
    (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K) a
  have c₁ : F.map ((homologyFunctorFactors C a').inv.app K) ≫
      F.map ((homologyFunctorFactors C a').hom.app K) = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id_app, F.map_id]
  have c₂ : (homologyFunctor D a).map
        (F.mapDerivedCategoryFactors.inv.app ((shiftFunctor (CochainComplex C ℤ) n).obj K)) ≫
      (homologyFunctor D a).map
        (F.mapDerivedCategoryFactors.hom.app ((shiftFunctor (CochainComplex C ℤ) n).obj K)) =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  simp only [Category.assoc, reassoc_of% c₁, reassoc_of% c₂]
  erw [reassoc_of% key]
  simp only [reassoc_of% hF', Iso.inv_hom_id_app_assoc]
  rfl

open DerivedCategory in
/-- The isomorphisms `H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` are compatible with the shift
sequence structure of the homology functors. -/
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n a a' : ℤ) (h : n + a = a')
    (X : DerivedCategory C) :
    F.map (((homologyFunctor C 0).shiftIso n a a' h).hom.app X) ≫
        (F.mapDerivedCategoryHomologyFunctorIso a').hom.app X =
      (F.mapDerivedCategoryHomologyFunctorIso a).hom.app (X⟦n⟧) ≫
        (homologyFunctor D a).map ((F.mapDerivedCategory.commShiftIso n).hom.app X) ≫
        ((homologyFunctor D 0).shiftIso n a a' h).hom.app (F.mapDerivedCategory.obj X) := by
  let τ₁ : shiftFunctor (DerivedCategory C) n ⋙ homologyFunctor C a ⋙ F ⟶
      F.mapDerivedCategory ⋙ homologyFunctor D a' :=
    Functor.whiskerRight ((homologyFunctor C 0).shiftIso n a a' h).hom F ≫
      (F.mapDerivedCategoryHomologyFunctorIso a').hom
  let τ₂ : shiftFunctor (DerivedCategory C) n ⋙ homologyFunctor C a ⋙ F ⟶
      F.mapDerivedCategory ⋙ homologyFunctor D a' :=
    Functor.whiskerLeft (shiftFunctor (DerivedCategory C) n)
        (F.mapDerivedCategoryHomologyFunctorIso a).hom ≫
      Functor.whiskerRight (F.mapDerivedCategory.commShiftIso n).hom (homologyFunctor D a) ≫
      Functor.whiskerLeft F.mapDerivedCategory ((homologyFunctor D 0).shiftIso n a a' h).hom
  have : τ₁ = τ₂ := Localization.natTrans_ext Q (HomologicalComplex.quasiIso C (.up ℤ))
    (fun K ↦ by
      simpa [τ₁, τ₂] using F.mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso_Q n a a' h K)
  simpa [τ₁, τ₂] using congr_app this X

set_option linter.flexible false in
open DerivedCategory in
/-- The isomorphisms `H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` are compatible with the
identifications `H^n(A[-n]) ≅ A`. -/
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (A : C) :
    (F.mapDerivedCategoryHomologyFunctorIso n).hom.app ((singleFunctor C n).obj A) ≫
        (homologyFunctor D n).map ((F.mapDerivedCategorySingleFunctor n).hom.app A) ≫
        (singleFunctorCompHomologyFunctorIso D n).hom.app (F.obj A) =
      F.map ((singleFunctorCompHomologyFunctorIso C n).hom.app A) := by
  have hc := F.mapHomologicalComplexHomologyIso_hom_app_single (.up ℤ) n A
  have hF' := homologyFunctorFactors_hom_naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app A) n
  have hs : (F.mapDerivedCategorySingleFunctor n).hom.app A =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (.up ℤ) n).obj A) ≫
        Q.map ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app A) := by
    simp [mapDerivedCategorySingleFunctor, singleFunctorIsoCompQ]
    erw [Category.id_comp]
  have hSC : (singleFunctorCompHomologyFunctorIso C n).hom.app A =
      (homologyFunctorFactors C n).hom.app ((HomologicalComplex.single C (.up ℤ) n).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) n).hom.app A := by
    simp [singleFunctorCompHomologyFunctorIso, singleFunctorsPostcompQIso_hom_hom]
  have hSD : (singleFunctorCompHomologyFunctorIso D n).hom.app (F.obj A) =
      (homologyFunctorFactors D n).hom.app ((HomologicalComplex.single D (.up ℤ) n).obj (F.obj A)) ≫
        (HomologicalComplex.homologyFunctorSingleIso D (.up ℤ) n).hom.app (F.obj A) := by
    simp [singleFunctorCompHomologyFunctorIso, singleFunctorsPostcompQIso_hom_hom]
  have hφ : (homologyFunctor D n).map (F.mapDerivedCategoryFactors.inv.app
      ((HomologicalComplex.single C (.up ℤ) n).obj A)) ≫
      (homologyFunctor D n).map (F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (.up ℤ) n).obj A)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  erw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  rw [hs, hSC, hSD, Functor.map_comp, F.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hφ, reassoc_of% hF', Iso.inv_hom_id_app_assoc, ← hc, Iso.inv_hom_id_app_assoc]

set_option linter.flexible false in
open DerivedCategory in
/-- The isomorphisms `F.mapDerivedCategorySingleFunctor` are compatible with the shifts. -/
lemma mapDerivedCategorySingleFunctor_hom_app_shiftIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n a a' : ℤ) (h : n + a = a')
    (A : C) :
    F.mapDerivedCategory.map (((singleFunctors C).shiftIso n a a' h).hom.app A) ≫
        (F.mapDerivedCategorySingleFunctor a).hom.app A =
      (F.mapDerivedCategory.commShiftIso n).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor a').hom.app A)⟦n⟧' ≫
        ((singleFunctors D).shiftIso n a a' h).hom.app (F.obj A) := by
  have hσC := congr_app ((singleFunctorsPostcompQIso C).hom.comm n a a' h) A
  have hσD := congr_app ((singleFunctorsPostcompQIso D).hom.comm n a a' h) (F.obj A)
  simp [singleFunctorsPostcompQIso_hom_hom] at hσC hσD
  have hs (b : ℤ) : (F.mapDerivedCategorySingleFunctor b).hom.app A =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (.up ℤ) b).obj A) ≫
        Q.map ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) b).hom.app A) := by
    simp [mapDerivedCategorySingleFunctor, singleFunctorIsoCompQ]
    erw [Category.id_comp]
  have hK := F.mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app n a a' h A
  have hφ := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom n
    ((HomologicalComplex.single C (.up ℤ) a').obj A)
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc] at hφ
  have hφ' : (F.mapDerivedCategory.commShiftIso n).hom.app
        (Q.obj ((HomologicalComplex.single C (.up ℤ) a').obj A)) ≫
      (F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (.up ℤ) a').obj A))⟦n⟧' =
      F.mapDerivedCategory.map ((Q.commShiftIso n).inv.app
          ((HomologicalComplex.single C (.up ℤ) a').obj A)) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((HomologicalComplex.single C (.up ℤ) a').obj A)⟦n⟧) ≫
        Q.map (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app
          ((HomologicalComplex.single C (.up ℤ) a').obj A)) ≫
        (Q.commShiftIso n).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj
            ((HomologicalComplex.single C (.up ℤ) a').obj A)) := by
    rw [← hφ, ← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp]
  have hnat := F.mapDerivedCategoryFactors.hom.naturality
    (((CochainComplex.singleFunctors C).shiftIso n a a' h).hom.app A)
  have hQ := Q.commShiftIso_hom_naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) a').hom.app A) n
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [hσC, hσD, hs, hs, F.mapDerivedCategory.map_comp_assoc]
  erw [reassoc_of% hnat]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hφ', ← reassoc_of% hQ, Iso.hom_inv_id_app_assoc]
  simp only [← Q.map_comp]
  erw [hK]
  rfl

/-- An exact functor `F` kills an object `K` of the derived category as soon as it kills all
the homology objects of `K`, since `H^n (F K) ≅ F (H^n K)`. -/
lemma isZero_mapDerivedCategory_obj (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : DerivedCategory C)
    (hK : ∀ n : ℤ, IsZero (F.obj ((DerivedCategory.homologyFunctor C n).obj K))) :
    IsZero (F.mapDerivedCategory.obj K) :=
  (DerivedCategory.isZero_iff _).2 fun n ↦
    (hK n).of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).symm.app K)

/-- If a family of exact functors jointly reflects isomorphisms, so does the family of the
induced functors on derived categories: a morphism is an isomorphism iff it is one on all
homology objects, and `F.mapDerivedCategory` commutes with homology. -/
lemma jointlyReflectIsomorphisms_mapDerivedCategory {I : Type*} {D' : I → Type*}
    [∀ i, Category (D' i)] [∀ i, Abelian (D' i)] [∀ i, HasDerivedCategory (D' i)]
    {F : ∀ i, C ⥤ D' i} [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [∀ i, PreservesFiniteColimits (F i)] (hF : JointlyReflectIsomorphisms F) :
    JointlyReflectIsomorphisms fun i ↦ (F i).mapDerivedCategory where
  isIso f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    exact (hF.isIso_iff _).2 fun i ↦
      (NatIso.isIso_map_iff ((F i).mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)

/-- If a pair of exact functors jointly reflects isomorphisms, so does the pair of the
induced functors on derived categories. This is the `CategoryTheory.pairFunctor` form of
`CategoryTheory.Functor.jointlyReflectIsomorphisms_mapDerivedCategory`. -/
lemma jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory {D₁ D₂ : Type u₁}
    [Category.{v₁} D₁] [Category.{v₁} D₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory D₁] [HasDerivedCategory D₂] (F₁ : C ⥤ D₁) (F₂ : C ⥤ D₂)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (hF : JointlyReflectIsomorphisms (pairFunctor F₁ F₂)) :
    JointlyReflectIsomorphisms (pairFunctor F₁.mapDerivedCategory F₂.mapDerivedCategory) := by
  refine jointlyReflectIsomorphisms_pairFunctor _ _ fun K L f h₁ h₂ ↦ ?_
  rw [DerivedCategory.isIso_iff]
  intro n
  refine hF.isIso_of_pairFunctor _ ?_ ?_ <;>
    exact (NatIso.isIso_map_iff (mapDerivedCategoryHomologyFunctorIso _ n) f).2
      (by rw [Functor.comp_map]; infer_instance)

section Plus

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor between abelian categories preserves bounded below objects of the
derived categories: an object isomorphic to a complex concentrated in degrees `≥ n` is
sent to an object with the same property. (blueprint: `situation-conventions`) -/
lemma isGE_mapDerivedCategory_obj (X : DerivedCategory C) (n : ℤ) [X.IsGE n] :
    (F.mapDerivedCategory.obj X).IsGE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  have : DerivedCategory.TStructure.t.IsGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj K) n :=
    inferInstanceAs (DerivedCategory.IsGE (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) n)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm n

/-- An exact functor between abelian categories sends an object of the derived category
whose `n`-th homology vanishes to an object whose `n`-th homology vanishes. -/
lemma isZero_homologyFunctor_mapDerivedCategory_obj {X : DerivedCategory C} {n : ℤ}
    (hX : IsZero ((DerivedCategory.homologyFunctor C n).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj X)) :=
  (F.map_isZero hX).of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).symm.app X)

/-- An exact functor between abelian categories preserves bounded above objects of the
derived categories: an object with homology concentrated in degrees `≤ n` is sent to an
object with the same property. -/
lemma isLE_mapDerivedCategory_obj (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n :=
  (DerivedCategory.isLE_iff _ n).2 fun i hi ↦
    F.isZero_homologyFunctor_mapDerivedCategory_obj ((DerivedCategory.isLE_iff X n).1 ‹_› i hi)

/-- An exact functor between abelian categories preserves homology concentration in an
interval `[a, b]`. -/
lemma homologyConcentratedIn_mapDerivedCategory_obj {a b : ℤ} {X : DerivedCategory C}
    (hX : DerivedCategory.homologyConcentratedIn a b X) :
    DerivedCategory.homologyConcentratedIn a b (F.mapDerivedCategory.obj X) := by
  obtain ⟨_, _⟩ := (DerivedCategory.homologyConcentratedIn_iff a b X).1 hX
  exact (DerivedCategory.homologyConcentratedIn_iff a b _).2
    ⟨F.isGE_mapDerivedCategory_obj X a, F.isLE_mapDerivedCategory_obj X b⟩

/-- An exact functor between abelian categories preserves objects of the derived categories
that are bounded for the canonical t-structure. -/
lemma bounded_mapDerivedCategory_obj {X : DerivedCategory C}
    (hX : DerivedCategory.TStructure.t.bounded X) :
    DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj X) := by
  obtain ⟨a, b, hab⟩ := (DerivedCategory.exists_homologyConcentratedIn_iff_bounded X).2 hX
  exact (DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
    ⟨a, b, F.homologyConcentratedIn_mapDerivedCategory_obj hab⟩

/-- A faithful exact functor between abelian categories reflects the vanishing of homology
objects in the derived categories. -/
lemma isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj [F.Faithful]
    {X : DerivedCategory C} {n : ℤ}
    (hX : IsZero ((DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj X))) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj X) := by
  have h := hX.of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app X)
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact F.map_injective (by simpa using h)

/-- A faithful exact functor between abelian categories reflects homology concentration in an
interval `[a, b]`: it reflects the vanishing of homology objects. -/
lemma homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj [F.Faithful]
    {a b : ℤ} {X : DerivedCategory C}
    (hX : DerivedCategory.homologyConcentratedIn a b (F.mapDerivedCategory.obj X)) :
    DerivedCategory.homologyConcentratedIn a b X := by
  obtain ⟨h₁, h₂⟩ := hX
  exact ⟨(DerivedCategory.isGE_iff X a).2 fun i hi ↦
      F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        ((DerivedCategory.isGE_iff _ a).1 h₁ i hi),
    (DerivedCategory.isLE_iff X b).2 fun i hi ↦
      F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        ((DerivedCategory.isLE_iff _ b).1 h₂ i hi)⟩

/-- A faithful exact functor between abelian categories reflects objects of the derived
categories that are bounded for the canonical t-structure. -/
lemma bounded_of_bounded_mapDerivedCategory_obj [F.Faithful] {X : DerivedCategory C}
    (hX : DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj X)) :
    DerivedCategory.TStructure.t.bounded X := by
  obtain ⟨a, b, hab⟩ := (DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 hX
  exact (DerivedCategory.exists_homologyConcentratedIn_iff_bounded X).1
    ⟨a, b, F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj hab⟩

/-- The functor induced on the bounded below derived categories by an exact functor
between abelian categories: the restriction of `F.mapDerivedCategory` to
`DerivedCategory.Plus`, which is well defined since an exact functor preserves bounded
below objects. (blueprint: `situation-conventions`) -/
noncomputable def mapDerivedCategoryPlus :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  DerivedCategory.TStructure.t.plus.lift
    (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (by
      rintro ⟨X, n, hn⟩
      exact ⟨n, F.isGE_mapDerivedCategory_obj X n⟩)

@[inherit_doc mapDerivedCategoryPlus]
scoped notation "D+(" F ")" => mapDerivedCategoryPlus F

/-- The restriction `F.mapDerivedCategoryPlus` of `F.mapDerivedCategory` to the bounded
below derived categories is compatible with the inclusions.
(blueprint: `situation-conventions`) -/
noncomputable def mapDerivedCategoryPlusCompatibility :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
  Iso.refl _

instance : F.mapDerivedCategoryPlus.Additive :=
  have : (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι).Additive :=
    Functor.additive_of_iso F.mapDerivedCategoryPlusCompatibility.symm
  Functor.additive_of_comp_faithful _ DerivedCategory.Plus.ι

/-- `F.mapDerivedCategoryPlus` commutes with shifts, as the restriction of the triangulated
functor `F.mapDerivedCategory`. -/
noncomputable instance : F.mapDerivedCategoryPlus.CommShift ℤ := by
  dsimp only [mapDerivedCategoryPlus]
  infer_instance

instance : F.mapDerivedCategoryPlus.IsTriangulated := by
  dsimp only [mapDerivedCategoryPlus]
  infer_instance

/-- The functor induced by an exact functor on the bounded below derived categories is t-exact
for the canonical t-structures. -/
instance : F.mapDerivedCategoryPlus.IsTExact DerivedCategory.Plus.TStructure.t
    DerivedCategory.Plus.TStructure.t where
  isLE X n _ := (DerivedCategory.Plus.isLE_ι_obj_iff (F.mapDerivedCategoryPlus.obj X) n).1
    (F.isLE_mapDerivedCategory_obj (DerivedCategory.Plus.ι.obj X) n)
  isGE X n _ := (DerivedCategory.Plus.isGE_ι_obj_iff (F.mapDerivedCategoryPlus.obj X) n).1
    (F.isGE_mapDerivedCategory_obj (DerivedCategory.Plus.ι.obj X) n)

/-- The functor `F.mapDerivedCategoryPlus` induced on the bounded below derived categories
by an exact functor `F` factors the functor `F.mapHomotopyCategoryPlus` on the bounded
below homotopy categories through the localization functors: the bounded below counterpart
of `Functor.mapDerivedCategoryFactorsh`. (blueprint: `situation-conventions`) -/
noncomputable def mapDerivedCategoryPlusFactorsh :
    DerivedCategory.Plus.Qh ⋙ F.mapDerivedCategoryPlus ≅
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft DerivedCategory.Plus.Qh F.mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh C) F.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (HomotopyCategory.Plus.ι C) F.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Iso.refl (HomotopyCategory.Plus.ι C ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ))).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft F.mapHomotopyCategoryPlus
        (DerivedCategory.Plus.QhCompιIsoιCompQh D).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The factorization `Functor.mapDerivedCategoryPlusFactorsh` is the restriction of
`Functor.mapDerivedCategoryFactorsh` along the fully faithful inclusion
`DerivedCategory.Plus.ι`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusFactorsh_hom_app (K : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) =
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.Plus.ι C).obj K) := by
  rw [mapDerivedCategoryPlusFactorsh, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility, DerivedCategory.Plus.QhCompιIsoιCompQh,
    DerivedCategory.Plus.Qh, mapDerivedCategoryPlus, mapHomotopyCategoryPlus,
    ObjectProperty.lift]

/-- The factorization `Functor.mapDerivedCategoryPlusFactorsh` commutes with the shifts. -/
instance : NatTrans.CommShift F.mapDerivedCategoryPlusFactorsh.hom ℤ := by
  have : Functor.whiskerRight F.mapDerivedCategoryPlusFactorsh.hom DerivedCategory.Plus.ι =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (DerivedCategory.TStructure.t.plus.liftCompιIso _ _).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.TStructure.t.plus.liftCompιIso _ _).hom
        F.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.ι C) F.mapDerivedCategoryFactorsh.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((HomotopyCategory.plus D).liftCompιIso _ _).inv
        DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F.mapHomotopyCategoryPlus
        (DerivedCategory.TStructure.t.plus.liftCompιIso _ _).inv ≫
      (Functor.associator _ _ _).inv := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, ObjectProperty.liftCompιIso,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.map_id, Category.id_comp]
    rw [F.ι_map_mapDerivedCategoryPlusFactorsh_hom_app K]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
      Category.id_comp, Category.comp_id]
    erw [Category.id_comp, Category.id_comp, Functor.map_id, Category.id_comp,
      Category.comp_id]
  have h₁ : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Plus.Qh
      (DerivedCategory.TStructure.t.plus.liftCompιIso (DerivedCategory.TStructure.t.plus.ι ⋙
        F.mapDerivedCategory) (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom) ℤ :=
    inferInstance
  have h₂ : NatTrans.CommShift (Functor.whiskerRight
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh)
        (fun X ↦ (DerivedCategory.Plus.Qh.obj X).2)).hom F.mapDerivedCategory) ℤ :=
    inferInstance
  have h₃ : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
      F.mapDerivedCategoryFactorsh.hom) ℤ := inferInstance
  have h₄ : NatTrans.CommShift (Functor.whiskerLeft F.mapHomotopyCategoryPlus
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        ((HomotopyCategory.plus D).ι ⋙ DerivedCategory.Qh)
        (fun X ↦ (DerivedCategory.Plus.Qh.obj X).2)).inv) ℤ :=
    inferInstance
  have : NatTrans.CommShift (Functor.whiskerRight F.mapDerivedCategoryPlusFactorsh.hom
      DerivedCategory.Plus.ι) ℤ := by
    rw [this]; infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

/-- An exact functor commutes with the homology functors of the bounded below derived
categories: the restriction of `Functor.mapDerivedCategoryHomologyFunctorIso` along the
inclusion `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusHomologyFunctorIso (n : ℤ) :
    DerivedCategory.Plus.homologyFunctor C n ⋙ F ≅
      F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n :=
  Functor.associator DerivedCategory.Plus.ι (DerivedCategory.homologyFunctor C n) F ≪≫
    isoWhiskerLeft DerivedCategory.Plus.ι (F.mapDerivedCategoryHomologyFunctorIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryPlusCompatibility.symm
      (DerivedCategory.homologyFunctor D n) ≪≫
    Functor.associator _ _ _

/-- An isomorphism `F ≅ G` of exact functors between abelian categories induces an
isomorphism `F.mapDerivedCategoryPlus ≅ G.mapDerivedCategoryPlus` of the functors
induced on the bounded below derived categories: the restriction of
`Functor.mapDerivedCategoryNatIso` along the inclusions `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategoryPlus ≅ G.mapDerivedCategoryPlus :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (F.mapDerivedCategoryPlusCompatibility ≪≫
      isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryNatIso e) ≪≫
      G.mapDerivedCategoryPlusCompatibility.symm)

/-- The isomorphism `Functor.mapDerivedCategoryPlusNatIso` is the restriction of
`Functor.mapDerivedCategoryNatIso` along the fully faithful inclusion
`DerivedCategory.Plus.ι`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusNatIso_hom_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatIso e).hom.app X) =
      (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusNatIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility, mapDerivedCategoryPlus, ObjectProperty.lift]

/-- The isomorphism `Functor.mapDerivedCategoryPlusNatIso` is characterized by its
compatibility with the factorizations `Functor.mapDerivedCategoryPlusFactorsh` through the
localization functors `DerivedCategory.Plus.Qh`: on the image of a bounded below complex it
is the levelwise image of `e`. -/
@[reassoc]
lemma mapDerivedCategoryPlusNatIso_hom_app_factorsh {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app K =
      F.mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hqh : ∀ {X Y : HomotopyCategory.Plus D} (g : X ⟶ Y),
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map g) =
        DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι D).map g) := fun _ => rfl
  have hnt : (HomotopyCategory.Plus.ι D).map
      ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) =
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  simp only [Functor.map_comp, hqh, hnt, ι_map_mapDerivedCategoryPlusFactorsh_hom_app,
    ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact mapDerivedCategoryNatIso_fach e ((HomotopyCategory.Plus.ι C).obj K)

/-- The composition isomorphism
`(F ⋙ G).mapDerivedCategoryPlus ≅ F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus`
for exact functors between abelian categories: the restriction of
`Functor.mapDerivedCategoryCompIso` along the inclusions `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategoryPlus ≅
      F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    ((F ⋙ G).mapDerivedCategoryPlusCompatibility ≪≫
      isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryPlusCompatibility.symm G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft F.mapDerivedCategoryPlus
        G.mapDerivedCategoryPlusCompatibility.symm ≪≫
      (Functor.associator _ _ _).symm)

section Comp

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The composition isomorphism `Functor.mapDerivedCategoryPlusCompIso` is the restriction of
`Functor.mapDerivedCategoryCompIso` along the fully faithful inclusion
`DerivedCategory.Plus.ι`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusCompIso_hom_app (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso F G).hom.app X) =
      (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusCompIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility, mapDerivedCategoryPlus, ObjectProperty.lift]

/-- The composition isomorphism `Functor.mapDerivedCategoryPlusCompIso` is characterized by
its compatibility with the factorizations `Functor.mapDerivedCategoryPlusFactorsh` through
the localization functors `DerivedCategory.Plus.Qh`. -/
@[reassoc]
lemma mapDerivedCategoryPlusCompIso_fac (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
    (F ⋙ G).mapDerivedCategoryPlusFactorsh.hom.app K := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map f) =
        G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  have hqh : ∀ {X Y : HomotopyCategory.Plus E} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map f) =
        DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι E).map f) := fun _ => rfl
  have hci : (HomotopyCategory.Plus.ι E).map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  simp only [Functor.map_comp, hmap, hqh, hci,
    ι_map_mapDerivedCategoryPlusFactorsh_hom_app, ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  exact mapDerivedCategoryCompIso_fach F G ((HomotopyCategory.Plus.ι C).obj K)

/-- The form of `Functor.mapDerivedCategoryPlusCompIso_fac` in which the comparison
isomorphism `Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))` on the bounded
below homotopy categories has been cancelled, it being the identity. -/
@[reassoc]
lemma mapDerivedCategoryPlusCompIso_hom_app_factorsh (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) =
      (F ⋙ G).mapDerivedCategoryPlusFactorsh.hom.app K := by
  have hqc : DerivedCategory.Plus.Qh.map
      ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
      𝟙 ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj
        (F.mapHomotopyCategoryPlus.obj K)) := by
    rw [mapHomotopyCategoryPlusCompIso_refl_hom_app]
    exact DerivedCategory.Plus.Qh.map_id _
  have key := mapDerivedCategoryPlusCompIso_fac F G K
  rwa [hqc, Category.comp_id] at key

/-- The isomorphism version of `Functor.mapDerivedCategoryPlusCompIso_fac`: the factorization
of `(F ⋙ G).mapDerivedCategoryPlus` through the localization functors
`DerivedCategory.Plus.Qh` is the composite of the composition isomorphism, the factorizations
of `F` and `G`, and the composition isomorphism of `mapHomotopyCategoryPlus`. -/
lemma mapDerivedCategoryPlusFactorsh_comp :
    (F ⋙ G).mapDerivedCategoryPlusFactorsh =
      isoWhiskerLeft DerivedCategory.Plus.Qh (mapDerivedCategoryPlusCompIso F G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight F.mapDerivedCategoryPlusFactorsh G.mapDerivedCategoryPlus ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F.mapHomotopyCategoryPlus G.mapDerivedCategoryPlusFactorsh ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G)))
          DerivedCategory.Plus.Qh := by
  ext K : 3
  simpa using (mapDerivedCategoryPlusCompIso_fac F G K).symm

end Comp

/-- `DerivedCategory.Plus.singleFunctor` commutes with an exact functor `F` and
`F.mapDerivedCategoryPlus`: the restriction of `Functor.mapDerivedCategorySingleFunctor`
along the inclusions `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusSingleFunctor (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙ F.mapDerivedCategoryPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor D n :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C n)
        F.mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso C n)
        F.mapDerivedCategory ≪≫
      F.mapDerivedCategorySingleFunctor n ≪≫
      isoWhiskerLeft F (DerivedCategory.Plus.singleFunctorιIso D n).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The image under the inclusion `D⁺ ⥤ D` of the commutation of `F.mapDerivedCategoryPlus` with
the shifts is the commutation of `F.mapDerivedCategory` with the shifts. -/
lemma ι_map_mapDerivedCategoryPlus_commShiftIso_hom_app (n : ℤ) (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((F.mapDerivedCategoryPlus.commShiftIso n).hom.app X) ≫
      (DerivedCategory.Plus.ι.commShiftIso n).hom.app (F.mapDerivedCategoryPlus.obj X) =
      F.mapDerivedCategory.map ((DerivedCategory.Plus.ι.commShiftIso n).hom.app X) ≫
        (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Plus.ι.obj X) := by
  have hc := NatTrans.shift_app_comm
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (fun Y ↦
        (F.mapDerivedCategoryPlus.obj Y).2)).hom n X
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app] at hc
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app] at hc
  erw [Functor.map_id, Category.comp_id, Category.id_comp] at hc
  exact hc

set_option linter.flexible false in
/-- The image under the inclusion `D⁺ ⥤ D` of `F.mapDerivedCategoryPlusSingleFunctor` is
`F.mapDerivedCategorySingleFunctor`. -/
lemma ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app (n : ℤ) (A : C) :
    DerivedCategory.Plus.ι.map ((F.mapDerivedCategoryPlusSingleFunctor n).hom.app A) =
      (F.mapDerivedCategorySingleFunctor n).hom.app A := by
  simp [mapDerivedCategoryPlusSingleFunctor, DerivedCategory.Plus.singleFunctorιIso,
    mapDerivedCategoryPlusCompatibility]
  erw [Category.id_comp, Category.comp_id]
  exact DerivedCategory.Plus.ι.map_preimage _

set_option linter.flexible false in
set_option linter.flexible false in
/-- The isomorphisms `H^n(-) ⋙ F ≅ F.mapDerivedCategoryPlus ⋙ H^n(-)` are compatible with the
shift sequence structure of the homology functors: they commute with the isomorphisms
`H^a(X⟦n⟧) ≅ H^{a'}(X)` for `n + a = a'`. -/
lemma mapDerivedCategoryPlusHomologyFunctorIso_hom_app_shiftIso (n a a' : ℤ) (h : n + a = a')
    (X : DerivedCategory.Plus C) :
    F.map (((DerivedCategory.Plus.homologyFunctor C 0).shiftIso n a a' h).hom.app X) ≫
        (F.mapDerivedCategoryPlusHomologyFunctorIso a').hom.app X =
      (F.mapDerivedCategoryPlusHomologyFunctorIso a).hom.app (X⟦n⟧) ≫
        (DerivedCategory.Plus.homologyFunctor D a).map
          ((F.mapDerivedCategoryPlus.commShiftIso n).hom.app X) ≫
        ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso n a a' h).hom.app
          (F.mapDerivedCategoryPlus.obj X) := by
  have hsC : ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso n a a' h).hom.app X =
      (DerivedCategory.homologyFunctor C a).map
        ((DerivedCategory.Plus.ι.commShiftIso n).hom.app X) ≫
      ((DerivedCategory.homologyFunctor C 0).shiftIso n a a' h).hom.app
        (DerivedCategory.Plus.ι.obj X) := by
    refine (Category.id_comp _).trans ?_
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app]
    erw [Category.id_comp]
    rfl
  have hsD : ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso n a a' h).hom.app
      (F.mapDerivedCategoryPlus.obj X) =
      (DerivedCategory.homologyFunctor D a).map
        ((DerivedCategory.Plus.ι.commShiftIso n).hom.app (F.mapDerivedCategoryPlus.obj X)) ≫
      ((DerivedCategory.homologyFunctor D 0).shiftIso n a a' h).hom.app
        (DerivedCategory.Plus.ι.obj (F.mapDerivedCategoryPlus.obj X)) := by
    refine (Category.id_comp _).trans ?_
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app]
    erw [Category.id_comp]
    rfl
  have he (m : ℤ) (Y : DerivedCategory.Plus C) :
      (F.mapDerivedCategoryPlusHomologyFunctorIso m).hom.app Y =
        (F.mapDerivedCategoryHomologyFunctorIso m).hom.app (DerivedCategory.Plus.ι.obj Y) := by
    simp [mapDerivedCategoryPlusHomologyFunctorIso, mapDerivedCategoryPlusCompatibility]
    erw [Functor.map_id, Category.comp_id, Category.id_comp]
  have hc := NatTrans.shift_app_comm
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (fun Y ↦
        (F.mapDerivedCategoryPlus.obj Y).2)).hom n X
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app] at hc
  have hc' : DerivedCategory.Plus.ι.map ((F.mapDerivedCategoryPlus.commShiftIso n).hom.app X) ≫
      (DerivedCategory.Plus.ι.commShiftIso n).hom.app (F.mapDerivedCategoryPlus.obj X) =
      F.mapDerivedCategory.map ((DerivedCategory.Plus.ι.commShiftIso n).hom.app X) ≫
        (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Plus.ι.obj X) := by
    simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app] at hc
    erw [Functor.map_id, Category.comp_id, Category.id_comp] at hc
    exact hc
  have hc'' := congrArg (DerivedCategory.homologyFunctor D a).map hc'
  simp only [Functor.map_comp] at hc''
  have := F.mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso n a a' h
    (DerivedCategory.Plus.ι.obj X)
  have ne := (F.mapDerivedCategoryHomologyFunctorIso a).hom.naturality
    ((DerivedCategory.Plus.ι.commShiftIso n).hom.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at ne
  rw [hsC, hsD, he, he, F.map_comp_assoc]
  erw [this, reassoc_of% ne, reassoc_of% hc'']
  rfl

set_option linter.flexible false in
set_option linter.flexible false in
/-- The isomorphism `H^n(F(A)[-n]) ≅ F(H^n(A[-n]))` given by `F.mapDerivedCategoryPlusSingleFunctor`
and `F.mapDerivedCategoryPlusHomologyFunctorIso` is compatible with the identifications
`H^n(A[-n]) ≅ A`. -/
lemma mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor (n : ℤ) (A : C) :
    (F.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
        ((DerivedCategory.Plus.singleFunctor C n).obj A) ≫
      (DerivedCategory.Plus.homologyFunctor D n).map
        ((F.mapDerivedCategoryPlusSingleFunctor n).hom.app A) ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app (F.obj A) =
    F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app A) := by
  have h₁ := F.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app n A
  have he : (F.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
      ((DerivedCategory.Plus.singleFunctor C n).obj A) =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom.app
        ((DerivedCategory.singleFunctor C n).obj A) := by
    simp [mapDerivedCategoryPlusHomologyFunctorIso, mapDerivedCategoryPlusCompatibility]
    erw [Functor.map_id, Category.comp_id, Category.id_comp]
    rfl
  rw [he]
  have := F.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor n A
  rw [← h₁] at this
  exact this

/-- The isomorphisms `F.mapDerivedCategoryPlusSingleFunctor` are compatible with the shifts. -/
lemma mapDerivedCategoryPlusSingleFunctor_hom_app_shiftIso (n a a' : ℤ) (h : n + a = a')
    (A : C) :
    F.mapDerivedCategoryPlus.map
        (((DerivedCategory.Plus.singleFunctors C).shiftIso n a a' h).hom.app A) ≫
      (F.mapDerivedCategoryPlusSingleFunctor a).hom.app A =
    (F.mapDerivedCategoryPlus.commShiftIso n).hom.app _ ≫
      ((F.mapDerivedCategoryPlusSingleFunctor a').hom.app A)⟦n⟧' ≫
      ((DerivedCategory.Plus.singleFunctors D).shiftIso n a a' h).hom.app (F.obj A) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hσC : DerivedCategory.Plus.ι.map
      (((DerivedCategory.Plus.singleFunctors C).shiftIso n a a' h).hom.app A) =
      (DerivedCategory.Plus.ι.commShiftIso n).hom.app
          ((DerivedCategory.Plus.singleFunctor C a').obj A) ≫
        ((DerivedCategory.singleFunctors C).shiftIso n a a' h).hom.app A := by
    erw [SingleFunctors.map_lift_shiftIso_hom_app]
    simp
    rfl
  have hσD : DerivedCategory.Plus.ι.map
      (((DerivedCategory.Plus.singleFunctors D).shiftIso n a a' h).hom.app (F.obj A)) =
      (DerivedCategory.Plus.ι.commShiftIso n).hom.app
          ((DerivedCategory.Plus.singleFunctor D a').obj (F.obj A)) ≫
        ((DerivedCategory.singleFunctors D).shiftIso n a a' h).hom.app (F.obj A) := by
    erw [SingleFunctors.map_lift_shiftIso_hom_app]
    simp
    rfl
  have hn := DerivedCategory.Plus.ι.commShiftIso_hom_naturality
    ((F.mapDerivedCategoryPlusSingleFunctor a').hom.app A) n
  have hc := F.ι_map_mapDerivedCategoryPlus_commShiftIso_hom_app n
    ((DerivedCategory.Plus.singleFunctor C a').obj A)
  have hD := F.mapDerivedCategorySingleFunctor_hom_app_shiftIso n a a' h A
  simp only [Functor.map_comp, hσD]
  erw [reassoc_of% hn, reassoc_of% hc, F.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    F.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  change F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map _) ≫ _ = _
  rw [hσC, F.mapDerivedCategory.map_comp_assoc]
  erw [hD]
  rfl

open DerivedCategory.Plus in
/-- The isomorphisms `τ_{≥ q} τ_{< q + 1} K ≅ H^q(K)[-q]` are compatible with the exact
functor `F`, through the commutation of the t-exact functor `F.mapDerivedCategoryPlus` with the
truncations and of `F` with the single functors and the homology functors. -/
lemma mapDerivedCategoryPlus_map_eTruncLTCompETruncGEIso_hom_app (q : ℤ)
    (K : DerivedCategory.Plus C) :
    F.mapDerivedCategoryPlus.map ((eTruncLTCompETruncGEIso q).hom.app K) ≫
      (F.mapDerivedCategoryPlusSingleFunctor q).hom.app ((homologyFunctor C q).obj K) ≫
      (singleFunctor D q).map ((F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K) =
    (F.mapDerivedCategoryPlus.eTruncGELTIsoApp TStructure.t TStructure.t q (q + 1 : ℤ) K).hom ≫
      (eTruncLTCompETruncGEIso q).hom.app (F.mapDerivedCategoryPlus.obj K) := by
  let t₁ := TStructure.t (C := C)
  let t₂ := TStructure.t (C := D)
  let Y := (t₁.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj K
  have : t₁.IsGE ((t₁.eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙ t₁.eTruncGE.obj (q : EInt)).obj K) q :=
    t₁.isGE_eTruncGE_obj_obj q q le_rfl _
  have : t₁.IsLE Y q := t₁.isLE_eTruncLT_obj_obj q ((q + 1 : ℤ) : EInt) le_rfl K
  have : t₁.IsLE ((t₁.eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙ t₁.eTruncGE.obj (q : EInt)).obj K) q :=
    inferInstanceAs (t₁.IsLE ((t₁.eTruncGE.obj (q : EInt)).obj Y) q)
  have : (F.mapDerivedCategoryPlus.obj ((t₁.eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙
      t₁.eTruncGE.obj (q : EInt)).obj K)).IsGE q :=
    Functor.IsTExact.isGE_obj t₁ t₂ F.mapDerivedCategoryPlus _ q
  have : (F.mapDerivedCategoryPlus.obj ((t₁.eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙
      t₁.eTruncGE.obj (q : EInt)).obj K)).IsLE q :=
    Functor.IsTExact.isLE_obj t₁ t₂ F.mapDerivedCategoryPlus _ q
  apply singleFunctor_hom_ext_of_isGE_of_isLE q
  have hs₂ {a b : D} (u : a ⟶ b) : (homologyFunctor D q).map ((singleFunctor D q).map u) ≫
      (singleFunctorCompHomologyFunctorIso (C := D) q).hom.app b =
      (singleFunctorCompHomologyFunctorIso (C := D) q).hom.app a ≫ u :=
    (singleFunctorCompHomologyFunctorIso (C := D) q).hom.naturality u
  have he {X₁ X₂ : DerivedCategory.Plus C} (f : X₁ ⟶ X₂) :
      (homologyFunctor D q).map (F.mapDerivedCategoryPlus.map f) =
        (F.mapDerivedCategoryPlusHomologyFunctorIso q).inv.app X₁ ≫
          F.map ((homologyFunctor C q).map f) ≫
          (F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app X₂ := by
    rw [← cancel_epi ((F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app X₁),
      Iso.hom_inv_id_app_assoc]
    exact ((F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.naturality f).symm
  have hC := F.mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor q
    ((homologyFunctor C q).obj K)
  have hε₁ := homologyFunctor_map_eTruncLTCompETruncGEIso_hom_app q K
  have hε₂ := homologyFunctor_map_eTruncLTCompETruncGEIso_hom_app q
    (F.mapDerivedCategoryPlus.obj K)
  rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso (C := D) q).hom.app
    ((homologyFunctor D q).obj (F.mapDerivedCategoryPlus.obj K)))]
  have hL : (homologyFunctor D q).map
        ((singleFunctor D q).map ((F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K)) ≫
      (singleFunctorCompHomologyFunctorIso (C := D) q).hom.app
        ((homologyFunctor D q).obj (F.mapDerivedCategoryPlus.obj K)) =
      (singleFunctorCompHomologyFunctorIso (C := D) q).hom.app
          (F.obj ((homologyFunctor C q).obj K)) ≫
        (F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K := hs₂ _
  have hC' : (homologyFunctor D q).map
        ((F.mapDerivedCategoryPlusSingleFunctor q).hom.app ((homologyFunctor C q).obj K)) ≫
      (singleFunctorCompHomologyFunctorIso (C := D) q).hom.app
        (F.obj ((homologyFunctor C q).obj K)) =
      (F.mapDerivedCategoryPlusHomologyFunctorIso q).inv.app
          ((singleFunctor C q).obj ((homologyFunctor C q).obj K)) ≫
        F.map ((singleFunctorCompHomologyFunctorIso (C := C) q).hom.app
          ((homologyFunctor C q).obj K)) := by
    rw [← hC, Iso.inv_hom_id_app_assoc]
  have : IsIso ((homologyFunctor D q).map
      (F.mapDerivedCategoryPlus.map ((t₁.eTruncGEπ (q : EInt)).app Y))) := by
    rw [he]; infer_instance
  have hκ : F.mapDerivedCategoryPlus.map ((t₁.eTruncGEπ (q : EInt)).app Y) ≫
      (F.mapDerivedCategoryPlus.eTruncGELTIsoApp t₁ t₂ q (q + 1 : ℤ) K).hom =
      (F.mapDerivedCategoryPlus.eTruncLTIsoApp t₁ t₂ ((q + 1 : ℤ) : EInt) K).hom ≫
        (t₂.eTruncGEπ (q : EInt)).app
          ((t₂.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj (F.mapDerivedCategoryPlus.obj K)) := by
    simp only [Functor.eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom]
    erw [Functor.eTruncGEπ_app_eTruncGEIsoApp_hom_assoc]
    exact t₂.eTruncGEπ_naturality _ _
  simp only [Functor.map_comp, Category.assoc, hL, reassoc_of% hC']
  rw [hε₂, he, ← cancel_epi ((homologyFunctor D q).map
    (F.mapDerivedCategoryPlus.map ((t₁.eTruncGEπ (q : EInt)).app Y)))]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hκ, Functor.map_comp_assoc, IsIso.hom_inv_id_assoc,
    ← Functor.map_comp, Functor.eTruncLTIsoApp_hom_eTruncLTι_app, he, he]
  have key : (homologyFunctor C q).map ((t₁.eTruncGEπ (q : EInt)).app Y) ≫
      (homologyFunctor C q).map ((eTruncLTCompETruncGEIso q).hom.app K) ≫
      (singleFunctorCompHomologyFunctorIso q).hom.app ((homologyFunctor C q).obj K) =
      (homologyFunctor C q).map ((t₁.eTruncLTι ((q + 1 : ℤ) : EInt)).app K) := by
    erw [hε₁, IsIso.hom_inv_id_assoc]
  have key' := congrArg F.map key
  simp only [F.map_comp] at key'
  erw [Iso.hom_inv_id_app_assoc]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% key']
  rfl

open DerivedCategory.Plus in
/-- The identification `τ_{≥ q} τ_{< q + 1} K ≅ H^q(K)[-q]` written with the single functor in
degree `0` is compatible with the exact functor `F`. -/
lemma mapDerivedCategoryPlus_eTruncGELTIsoApp_eTruncLTCompETruncGEIso (q : ℤ)
    (K : DerivedCategory.Plus C) {K' : DerivedCategory.Plus D}
    (ψ : F.mapDerivedCategoryPlus.obj K ⟶ K') :
    (F.mapDerivedCategoryPlus.eTruncGELTIsoApp TStructure.t TStructure.t q (q + 1 : ℤ) K).hom ≫
      (TStructure.t.eTruncGE.obj (q : EInt)).map
        ((TStructure.t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).map ψ) ≫
      (eTruncLTCompETruncGEIso q).hom.app K' ≫
      ((singleFunctors D).shiftIso (-q) q 0 (by simp)).inv.app ((homologyFunctor D q).obj K') =
    F.mapDerivedCategoryPlus.map ((eTruncLTCompETruncGEIso q).hom.app K) ≫
      F.mapDerivedCategoryPlus.map
        (((singleFunctors C).shiftIso (-q) q 0 (by simp)).inv.app ((homologyFunctor C q).obj K)) ≫
      (F.mapDerivedCategoryPlus.commShiftIso (-q)).hom.app
        ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)) ≫
      ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app ((homologyFunctor C q).obj K))⟦-q⟧' ≫
      ((singleFunctor D 0).map ((F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K ≫
        (homologyFunctor D q).map ψ))⟦-q⟧' := by
  have h₁ := (eTruncLTCompETruncGEIso (C := D) q).hom.naturality ψ
  have h₂ := ((singleFunctors D).shiftIso (-q) q 0 (by simp)).inv.naturality
    ((F.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K ≫ (homologyFunctor D q).map ψ)
  have h₃ := F.mapDerivedCategoryPlus_map_eTruncLTCompETruncGEIso_hom_app q K
  have h₄ := F.mapDerivedCategoryPlusSingleFunctor_hom_app_shiftIso (-q) q 0 (by simp)
    ((homologyFunctor C q).obj K)
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  have h₄' : (F.mapDerivedCategoryPlusSingleFunctor q).hom.app ((homologyFunctor C q).obj K) ≫
      ((singleFunctors D).shiftIso (-q) q 0 (by simp)).inv.app
        (F.obj ((homologyFunctor C q).obj K)) =
      F.mapDerivedCategoryPlus.map
        (((singleFunctors C).shiftIso (-q) q 0 (by simp)).inv.app ((homologyFunctor C q).obj K)) ≫
      (F.mapDerivedCategoryPlus.commShiftIso (-q)).hom.app
        ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)) ≫
      ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app ((homologyFunctor C q).obj K))⟦-q⟧' := by
    rw [← cancel_epi (F.mapDerivedCategoryPlus.map
      (((singleFunctors C).shiftIso (-q) q 0 (by simp)).hom.app ((homologyFunctor C q).obj K))),
      reassoc_of% h₄]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
    erw [Category.comp_id]
  rw [reassoc_of% h₁, ← reassoc_of% h₃, ← Functor.map_comp_assoc, h₂, reassoc_of% h₄']

end Plus

section Identity

variable (C)

/-- The characterization of `Functor.mapDerivedCategoryIdIso` at the level of the homotopy
category: the isomorphism `DerivedCategory.Qh ⋙ (𝟭 C).mapDerivedCategory ≅ DerivedCategory.Qh`
it induces is the one coming from `Functor.mapDerivedCategoryFactorsh` and
`Functor.mapHomotopyCategoryIdIso`. -/
lemma mapDerivedCategoryIdIso_factorsh :
    isoWhiskerLeft DerivedCategory.Qh (mapDerivedCategoryIdIso C) ≪≫
        DerivedCategory.Qh.rightUnitor =
      (𝟭 C).mapDerivedCategoryFactorsh ≪≫
        isoWhiskerRight (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        DerivedCategory.Qh.leftUnitor := by
  ext X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  dsimp
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app K)]
  simpa [mapDerivedCategoryFactorsh_hom_app, mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv, mapDerivedCategoryIdIso_hom_app,
    mapHomotopyCategoryIdIso_hom_app, DerivedCategory.quotientCompQhIso_hom_naturality,
    Category.assoc] using
    ((mapDerivedCategoryIdIso C).hom.naturality
      ((DerivedCategory.quotientCompQhIso C).hom.app K)).symm

/-- The functor induced on the bounded below derived categories by the identity functor is
isomorphic to the identity functor: the restriction of `Functor.mapDerivedCategoryIdIso`
along the inclusion `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusIdIso :
    (𝟭 C).mapDerivedCategoryPlus ≅ 𝟭 (DerivedCategory.Plus C) :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    ((𝟭 C).mapDerivedCategoryPlusCompatibility ≪≫
      isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryIdIso C) ≪≫
      DerivedCategory.Plus.ι.rightUnitor ≪≫ DerivedCategory.Plus.ι.leftUnitor.symm)

@[simp]
lemma ι_map_mapDerivedCategoryPlusIdIso_hom_app (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusIdIso C).hom.app X) =
      (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusIdIso, fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility]

/-- The characterization of `Functor.mapDerivedCategoryPlusIdIso` at the level of the bounded
below homotopy category: the isomorphism
`DerivedCategory.Plus.Qh ⋙ (𝟭 C).mapDerivedCategoryPlus ≅ DerivedCategory.Plus.Qh` it induces
is the one coming from `Functor.mapDerivedCategoryPlusFactorsh` and
`Functor.mapHomotopyCategoryPlusIdIso`. -/
lemma mapDerivedCategoryPlusIdIso_factorsh :
    isoWhiskerLeft DerivedCategory.Plus.Qh (mapDerivedCategoryPlusIdIso C) ≪≫
        DerivedCategory.Plus.Qh.rightUnitor =
      (𝟭 C).mapDerivedCategoryPlusFactorsh ≪≫
        isoWhiskerRight (mapHomotopyCategoryPlusIdIso C) DerivedCategory.Plus.Qh ≪≫
        DerivedCategory.Plus.Qh.leftUnitor := by
  apply Iso.ext
  ext K : 2
  apply DerivedCategory.Plus.ι.map_injective
  have h := congr_app (congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.Plus.ι C).obj K)
  have h' : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K)) =
      DerivedCategory.Qh.map
        ((mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app K.obj) :=
    congrArg DerivedCategory.Qh.map (ι_map_mapHomotopyCategoryPlusIdIso_hom_app C K)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_hom_app, Functor.map_comp, h',
    ι_map_mapDerivedCategoryPlusIdIso_hom_app, ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at h ⊢
  exact h

/-- The pointwise form of `Functor.mapDerivedCategoryPlusIdIso_factorsh`: on the image of a
bounded below homotopy category object, the identity isomorphism
`Functor.mapDerivedCategoryPlusIdIso` is the factorization
`Functor.mapDerivedCategoryPlusFactorsh` of `𝟭 C` followed by
`Functor.mapHomotopyCategoryPlusIdIso`. -/
@[reassoc]
lemma mapDerivedCategoryPlusIdIso_fac_app (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K) := by
  have := congr_app (congr_arg Iso.hom (mapDerivedCategoryPlusIdIso_factorsh C)) K
  simpa using this

/-- The form of `Functor.mapDerivedCategoryPlusIdIso_fac_app` in which the comparison
isomorphism `Functor.mapHomotopyCategoryPlusIdIso` on the bounded below homotopy categories
has been cancelled, it being the identity. -/
@[reassoc]
lemma mapDerivedCategoryPlusIdIso_hom_app_factorsh (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryPlusFactorsh.hom.app K := by
  have hq : DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K) =
      𝟙 (((𝟭 C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj K) := by
    rw [mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
    exact DerivedCategory.Plus.Qh.map_id _
  rw [mapDerivedCategoryPlusIdIso_fac_app, hq, Category.comp_id]

end Identity

section Coherence

/-- The left unit law for `Functor.mapDerivedCategoryPlusCompIso`: composing with the
identity isomorphism `Functor.mapDerivedCategoryPlusIdIso` in the first variable gives the
identity. -/
lemma mapDerivedCategoryPlusCompIso_id_comp (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (mapDerivedCategoryPlusCompIso (𝟭 C) F).hom ≫
        Functor.whiskerRight (mapDerivedCategoryPlusIdIso C).hom F.mapDerivedCategoryPlus =
      𝟙 F.mapDerivedCategoryPlus := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app]
  rw [← cancel_mono (F.mapDerivedCategoryPlusFactorsh.hom.app K),
    mapDerivedCategoryPlusIdIso_hom_app_factorsh, Category.assoc]
  exact (mapDerivedCategoryPlusCompIso_hom_app_factorsh (𝟭 C) F K).trans
    (Category.id_comp _).symm

/-- The right unit law for `Functor.mapDerivedCategoryPlusCompIso`: composing with the
identity isomorphism `Functor.mapDerivedCategoryPlusIdIso` in the second variable gives the
identity. -/
lemma mapDerivedCategoryPlusCompIso_comp_id (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (mapDerivedCategoryPlusCompIso F (𝟭 D)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategoryPlus (mapDerivedCategoryPlusIdIso D).hom =
      𝟙 F.mapDerivedCategoryPlus := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  have hnat : (mapDerivedCategoryPlusIdIso D).hom.app
        (F.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      F.mapDerivedCategoryPlusFactorsh.hom.app K =
      (𝟭 D).mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (mapDerivedCategoryPlusIdIso D).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) :=
    ((mapDerivedCategoryPlusIdIso D).hom.naturality _).symm
  rw [← cancel_mono (F.mapDerivedCategoryPlusFactorsh.hom.app K), Category.assoc, hnat,
    mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  exact (mapDerivedCategoryPlusCompIso_hom_app_factorsh F (𝟭 D) K).trans
    (Category.id_comp _).symm

variable {E' : Type*} [Category E'] [Abelian E'] [HasDerivedCategory E']

/-- The associativity law for `Functor.mapDerivedCategoryPlusCompIso`: the two ways of
comparing `(F ⋙ G ⋙ H).mapDerivedCategoryPlus` with
`F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ⋙ H.mapDerivedCategoryPlus` agree. -/
lemma mapDerivedCategoryPlusCompIso_assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    (mapDerivedCategoryPlusCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategoryPlus
          (mapDerivedCategoryPlusCompIso G H).hom =
      (mapDerivedCategoryPlusCompIso (F ⋙ G) H).hom ≫
        Functor.whiskerRight (mapDerivedCategoryPlusCompIso F G).hom
          H.mapDerivedCategoryPlus := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hnat : (mapDerivedCategoryPlusCompIso G H).hom.app
        (F.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      H.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlus.map
        (F.mapDerivedCategoryPlusFactorsh.hom.app K)) =
      (G ⋙ H).mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (mapDerivedCategoryPlusCompIso G H).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) :=
    ((mapDerivedCategoryPlusCompIso G H).hom.naturality _).symm
  rw [← cancel_mono (H.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlus.map
      (F.mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
    H.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app
      (F.mapHomotopyCategoryPlus.obj K)) ≫
    H.mapDerivedCategoryPlusFactorsh.hom.app
      (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)))]
  trans (F ⋙ G ⋙ H).mapDerivedCategoryPlusFactorsh.hom.app K
  · rw [Category.assoc, reassoc_of% hnat,
      mapDerivedCategoryPlusCompIso_hom_app_factorsh G H (F.mapHomotopyCategoryPlus.obj K)]
    exact mapDerivedCategoryPlusCompIso_hom_app_factorsh F (G ⋙ H) K
  · symm
    rw [Category.assoc]
    simp only [← Functor.map_comp_assoc]
    rw [mapDerivedCategoryPlusCompIso_hom_app_factorsh F G K]
    exact mapDerivedCategoryPlusCompIso_hom_app_factorsh (F ⋙ G) H K

end Coherence

end CategoryTheory.Functor

namespace CategoryTheory.Equivalence

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- An equivalence `E : C ≌ D` of abelian categories induces an equivalence
`D(C) ≌ D(D)` of derived categories, with functor `D(E.functor)` and inverse
`D(E.inverse)`. -/
noncomputable def mapDerivedCategory (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive] :
    DerivedCategory C ≌ DerivedCategory D :=
  Equivalence.mk E.functor.mapDerivedCategory E.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso C).symm ≪≫ Functor.mapDerivedCategoryNatIso E.unitIso ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso E.counitIso ≪≫ Functor.mapDerivedCategoryIdIso D)

end CategoryTheory.Equivalence

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- The functor `D(F)` induced on derived categories by an additive equivalence `F` of abelian
categories is an equivalence, with quasi-inverse `D(F⁻¹)`. -/
instance isEquivalence_mapDerivedCategory (F : C ⥤ D) [F.IsEquivalence] [F.Additive] :
    F.mapDerivedCategory.IsEquivalence :=
  have : F.asEquivalence.functor.Additive := ‹F.Additive›
  inferInstanceAs F.asEquivalence.mapDerivedCategory.functor.IsEquivalence

end CategoryTheory.Functor

namespace CategoryTheory.Functor

open DerivedCategory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

attribute [local instance] isLE_mapDerivedCategory_obj

/-- An isomorphism in degree `m` of homology between two objects whose `m`-th homology
vanishes. -/
private lemma isIso_homologyMap_of_isZero {X Y : DerivedCategory D} (f : X ⟶ Y) (m : ℤ)
    (hX : IsZero ((homologyFunctor D m).obj X)) (hY : IsZero ((homologyFunctor D m).obj Y)) :
    IsIso ((homologyFunctor D m).map f) :=
  ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

/-- An exact functor commutes with homology on morphisms: `Hᵐ(D(F) f)` is an isomorphism if
`Hᵐ f` is. -/
private lemma isIso_homologyMap_mapDerivedCategory {X Y : DerivedCategory C} (f : X ⟶ Y)
    (m : ℤ) [IsIso ((homologyFunctor C m).map f)] :
    IsIso ((homologyFunctor D m).map (F.mapDerivedCategory.map f)) := by
  have : IsIso ((homologyFunctor C m ⋙ F).map f) := by rw [Functor.comp_map]; infer_instance
  exact (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso m) f).1 this

/-- An exact functor `F` commutes with the truncation `τ^{≤ n}` of the canonical t-structure:
`D(F)(τ^{≤ n} X) ⟶ τ^{≤ n} D(F)(X)`, the factorisation of `D(F)` of the truncation map, is an
isomorphism, both sides having the homology of `D(F)(X)` in degrees `≤ n` and none above. -/
noncomputable def mapDerivedCategoryTruncLEIso (n : ℤ) :
    TStructure.t.truncLE n ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ TStructure.t.truncLE n :=
  NatIso.ofComponents
    (fun X ↦
      have : IsIso (TStructure.t.liftTruncLE
          (F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app X)) n) := by
        rw [isIso_iff]
        intro m
        by_cases hm : m ≤ n
        · have h₁ : ∀ Z : DerivedCategory C,
              IsIso ((homologyFunctor C m).map ((TStructure.t.truncLEι n).app Z)) := fun Z ↦
            have : ((TStructure.t.triangleLEGT n).obj Z).obj₃.IsGE (n + 1) :=
              (inferInstance : TStructure.t.IsGE ((TStructure.t.truncGT n).obj Z) (n + 1))
            isIso_homologyMap_mor₁ _ (TStructure.t.triangleLEGT_distinguished n Z) (m - 1) m
              (by lia) (isZero_of_isGE _ (n + 1) _ (by lia)) (isZero_of_isGE _ (n + 1) _ (by lia))
          have h₂ : ∀ Z : DerivedCategory D,
              IsIso ((homologyFunctor D m).map ((TStructure.t.truncLEι n).app Z)) := fun Z ↦
            have : ((TStructure.t.triangleLEGT n).obj Z).obj₃.IsGE (n + 1) :=
              (inferInstance : TStructure.t.IsGE ((TStructure.t.truncGT n).obj Z) (n + 1))
            isIso_homologyMap_mor₁ _ (TStructure.t.triangleLEGT_distinguished n Z) (m - 1) m
              (by lia) (isZero_of_isGE _ (n + 1) _ (by lia)) (isZero_of_isGE _ (n + 1) _ (by lia))
          have := F.isIso_homologyMap_mapDerivedCategory ((TStructure.t.truncLEι n).app X) m
          have := h₂ (F.mapDerivedCategory.obj X)
          have : IsIso ((homologyFunctor D m).map (TStructure.t.liftTruncLE
              (F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app X)) n) ≫
              (homologyFunctor D m).map
                ((TStructure.t.truncLEι n).app (F.mapDerivedCategory.obj X))) := by
            have hc : TStructure.t.liftTruncLE
                (F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app X)) n ≫
                  (TStructure.t.truncLEι n).app (F.mapDerivedCategory.obj X) =
                F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app X) :=
              TStructure.t.liftTruncLE_ι _ _
            rw [← Functor.map_comp, hc]
            infer_instance
          exact IsIso.of_isIso_comp_right _
            ((homologyFunctor D m).map ((TStructure.t.truncLEι n).app (F.mapDerivedCategory.obj X)))
        · exact isIso_homologyMap_of_isZero _ m (isZero_of_isLE _ n _ (by lia))
            (isZero_of_isLE _ n _ (by lia))
      asIso (TStructure.t.liftTruncLE
        (F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app X)) n))
    (fun {X Y} f ↦ by
      refine TStructure.t.to_truncLE_obj_ext (Y := F.mapDerivedCategory.obj
        ((TStructure.t.truncLE n).obj X)) ?_
      have hX : TStructure.t.liftTruncLE
          (F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app X)) n ≫
            (TStructure.t.truncLEι n).app (F.mapDerivedCategory.obj X) =
          F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app X) :=
        TStructure.t.liftTruncLE_ι _ _
      have hY : TStructure.t.liftTruncLE
          (F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app Y)) n ≫
            (TStructure.t.truncLEι n).app (F.mapDerivedCategory.obj Y) =
          F.mapDerivedCategory.map ((TStructure.t.truncLEι n).app Y) :=
        TStructure.t.liftTruncLE_ι _ _
      have nat₁ := (TStructure.t.truncLEι n).naturality f
      have nat₂ := (TStructure.t.truncLEι n).naturality (F.mapDerivedCategory.map f)
      simp only [Functor.id_map] at nat₁ nat₂
      simp only [Functor.comp_obj, Functor.comp_map, asIso_hom, Category.assoc]
      rw [hY, nat₂, reassoc_of% hX, ← Functor.map_comp, ← Functor.map_comp, nat₁])

attribute [local instance] isGE_mapDerivedCategory_obj

/-- An exact functor `F` commutes with the truncation `τ^{≥ n}` of the canonical t-structure:
`τ^{≥ n} D(F)(X) ⟶ D(F)(τ^{≥ n} X)`, the factorisation of `D(F)` of the truncation map, is an
isomorphism, both sides having the homology of `D(F)(X)` in degrees `≥ n` and none below. -/
noncomputable def mapDerivedCategoryTruncGEIso (n : ℤ) :
    TStructure.t.truncGE n ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ TStructure.t.truncGE n :=
  (NatIso.ofComponents
    (fun X ↦
      have : IsIso (TStructure.t.descTruncGE
          (F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app X)) n) := by
        rw [isIso_iff]
        intro m
        by_cases hm : n ≤ m
        · have h₂ : ∀ Z : DerivedCategory D,
              IsIso ((homologyFunctor D m).map ((TStructure.t.truncGEπ n).app Z)) := fun Z ↦
            isIso_homologyMap_mor₂ _ (TStructure.t.triangleLTGE_distinguished n Z) m (m + 1)
              rfl (isZero_of_isLE _ (n - 1) _ (by lia)) (isZero_of_isLE _ (n - 1) _ (by lia))
          have h₁ : IsIso ((homologyFunctor C m).map ((TStructure.t.truncGEπ n).app X)) :=
            isIso_homologyMap_mor₂ _ (TStructure.t.triangleLTGE_distinguished n X) m (m + 1)
              rfl (isZero_of_isLE _ (n - 1) _ (by lia)) (isZero_of_isLE _ (n - 1) _ (by lia))
          have := F.isIso_homologyMap_mapDerivedCategory ((TStructure.t.truncGEπ n).app X) m
          have := h₂ (F.mapDerivedCategory.obj X)
          have hc : (TStructure.t.truncGEπ n).app (F.mapDerivedCategory.obj X) ≫
              TStructure.t.descTruncGE
                (F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app X)) n =
              F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app X) :=
            TStructure.t.π_descTruncGE _ _
          have : IsIso ((homologyFunctor D m).map
              ((TStructure.t.truncGEπ n).app (F.mapDerivedCategory.obj X)) ≫
              (homologyFunctor D m).map (TStructure.t.descTruncGE
                (F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app X)) n)) := by
            rw [← Functor.map_comp, hc]
            infer_instance
          exact IsIso.of_isIso_comp_left
            ((homologyFunctor D m).map ((TStructure.t.truncGEπ n).app (F.mapDerivedCategory.obj X)))
            _
        · exact isIso_homologyMap_of_isZero _ m (isZero_of_isGE _ n _ (by lia))
            (isZero_of_isGE _ n _ (by lia))
      asIso (TStructure.t.descTruncGE
        (F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app X)) n))
    (fun {X Y} f ↦ by
      refine TStructure.t.from_truncGE_obj_ext (Y := F.mapDerivedCategory.obj
        ((TStructure.t.truncGE n).obj Y)) ?_
      have hX : (TStructure.t.truncGEπ n).app (F.mapDerivedCategory.obj X) ≫
          TStructure.t.descTruncGE
            (F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app X)) n =
          F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app X) :=
        TStructure.t.π_descTruncGE _ _
      have hY : (TStructure.t.truncGEπ n).app (F.mapDerivedCategory.obj Y) ≫
          TStructure.t.descTruncGE
            (F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app Y)) n =
          F.mapDerivedCategory.map ((TStructure.t.truncGEπ n).app Y) :=
        TStructure.t.π_descTruncGE _ _
      have nat₁ := (TStructure.t.truncGEπ n).naturality f
      have nat₂ := (TStructure.t.truncGEπ n).naturality (F.mapDerivedCategory.map f)
      simp only [Functor.id_map] at nat₁ nat₂
      simp only [Functor.comp_obj, Functor.comp_map, asIso_hom]
      rw [reassoc_of% hX, ← reassoc_of% nat₂, hY, ← Functor.map_comp, ← Functor.map_comp,
        nat₁])).symm

end CategoryTheory.Functor

namespace CategoryTheory.Functor

open Limits

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₁ ⥤ C₂) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor induces a triangulated functor on derived categories.** For an exact
functor `F` of abelian categories, the functor `F.mapDerivedCategory : D(C₁) ⥤ D(C₂)` obtained by
applying `F` termwise is triangulated, and it carries a complex `A[n]` concentrated in one
degree to `F(A)[n]` (`Functor.mapDerivedCategorySingleFunctor`).
(blueprint: `situation-conventions`) -/
theorem mapDerivedCategory_isTriangulated_and_singleFunctor :
    F.mapDerivedCategory.IsTriangulated ∧ ∀ n : ℤ,
      Nonempty (DerivedCategory.singleFunctor C₁ n ⋙ F.mapDerivedCategory ≅
        F ⋙ DerivedCategory.singleFunctor C₂ n) :=
  ⟨inferInstance, fun n ↦ ⟨F.mapDerivedCategorySingleFunctor n⟩⟩

/-- **The derived functor of an exact functor and its factorization.** For an exact functor `F`
of abelian categories, applying `F` termwise to cochain complexes preserves
quasi-isomorphisms; the induced functor `F.mapDerivedCategory` commutes with the shifts and is
triangulated; and the isomorphism `F.mapDerivedCategoryFactors :
Q ⋙ F.mapDerivedCategory ≅ F.mapHomologicalComplex _ ⋙ Q` is compatible with the shifts. In
particular `F` applied termwise to a complex `K` represents `F.mapDerivedCategory (Q K)`.
(blueprint: `situation-conventions`) -/
theorem mapDerivedCategoryFactors_commShift :
    (∀ {K L : CochainComplex C₁ ℤ} (f : K ⟶ L), QuasiIso f →
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ∧
    F.mapDerivedCategory.IsTriangulated ∧
    NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ :=
  ⟨fun _ _ ↦ inferInstance, inferInstance, inferInstance⟩

end CategoryTheory.Functor
