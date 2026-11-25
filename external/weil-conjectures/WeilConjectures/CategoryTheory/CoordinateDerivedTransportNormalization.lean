/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
import all WeilConjectures.CategoryTheory.RightDerivedBaseChangeSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.HomotopyCategory
import all Mathlib.CategoryTheory.Shift.InducedShiftSequence
import all WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalRealizationShift

/-! # Normalization of section transport

Source: Stacks Tag 05TD, the derived augmentation equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' d
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasDerivedCategory.{w'} C']
  [EnoughInjectives C] [EnoughInjectives C']
  {D : Type d} [Category D] [Abelian D] [HasDerivedCategory D]

/-- Derived transport with the derived identity comparison removed.
Source: Stacks Tag 05TD (blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
def coordinateSectionTransport
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E') :
    E.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ E'.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso D)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := E) (G' := E') (β := L) (γ := 𝟭 D) ((Functor.rightUnitor _).hom ≫ τ)

private theorem coordinate_id_shift :
    NatTrans.CommShift (Functor.mapDerivedCategoryPlusIdIso D).hom ℤ := by
  have hh : whiskerRight (mapDerivedCategoryPlusIdIso D).hom DerivedCategory.Plus.ι =
      (𝟭 D).mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryIdIso D).hom ≫
        DerivedCategory.Plus.ι.rightUnitor.hom ≫ DerivedCategory.Plus.ι.leftUnitor.inv := by
    ext K
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id]
    erw [ι_map_mapDerivedCategoryPlusIdIso_hom_app]
    simp only [mapDerivedCategoryPlusCompatibility,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    exact (Category.comp_id _).symm
  have := AlgebraicGeometry.ProEtale.exactCompatibility_shift (𝟭 D)
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusIdIso D).hom DerivedCategory.Plus.ι) ℤ := by
    rw [hh]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

/-- Normalized section transport respects shifts.
Source: Stacks Tag 05TD.
Proof: the identity comparison respects shifts after the faithful bounded-below
inclusion, where it is the proved unbounded identity comparison. Its inverse,
whiskering and composition with the base-change transformation preserve this property.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateSectionTransport_shift
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E') :
    NatTrans.CommShift (coordinateSectionTransport L E E' τ) ℤ := by
  have := coordinate_id_shift (D := D)
  have : NatTrans.CommShift (CategoryTheory.inv (mapDerivedCategoryPlusIdIso D).hom) ℤ :=
    NatTrans.CommShift.of_isIso (mapDerivedCategoryPlusIdIso D).hom ℤ
  have : NatTrans.CommShift (mapDerivedCategoryPlusIdIso D).inv ℤ := by
    have he : CategoryTheory.inv (mapDerivedCategoryPlusIdIso D).hom =
        (mapDerivedCategoryPlusIdIso D).inv :=
      IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id _)
    rw [he] at this
    exact this
  unfold coordinateSectionTransport
  simp only [Functor.isoWhiskerLeft_inv]
  infer_instance

private theorem coordinate_id_single (Y : D) :
    ((𝟭 D).mapDerivedCategoryPlusSingleFunctor 0).hom.app Y =
      (mapDerivedCategoryPlusIdIso D).hom.app
        ((DerivedCategory.Plus.singleFunctor D 0).obj Y) := by
  have ht := single_exact_transport (𝟭 D) Y
  simp only [singleTransport_hom, Functor.map_id, Category.id_comp,
    Category.comp_id] at ht
  have hi : (homotopySingleIso (𝟭 D) Y).hom = 𝟙 _ := by
    apply (HomotopyCategory.Plus.ι D).map_injective
    simp only [homotopySingleIso, Functor.preimageIso_hom, Functor.map_preimage,
      Functor.mapIso_hom]
    have hs : (HomologicalComplex.singleMapHomologicalComplex (𝟭 D)
        (ComplexShape.up ℤ) 0).hom.app Y = 𝟙 _ := by
      ext n
      by_cases hn : n = 0
      · subst n
        simp
      · exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 Y n hn).eq_of_src _ _
    change (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex (𝟭 D)
        (ComplexShape.up ℤ) 0).hom.app Y) = _
    erw [hs, Functor.map_id]
  erw [hi, Functor.map_id, Category.comp_id] at ht
  erw [ht, ← mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  rfl

/-- The normalized transport carries the derived augmentation to the target augmentation.
Source: Stacks Tag 05TD.
Proof: the unnormalized single-complex equation is `rightDerivedBaseChange_single_unit`.
Move the inverse identity comparison across the source augmentation by naturality.
Its value on a single object is the exact identity single comparison, so these
comparisons cancel. This proves the equation before taking any homology.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateSectionTransport_single_unit
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E')
    (Y : C) :
    E.rightDerivedPlusSingleUnit Y ≫
        (coordinateSectionTransport L E E' τ).app
          ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≫
        E'.rightDerivedFunctorPlus.map ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y) =
      (DerivedCategory.Plus.singleFunctor D 0).map (τ.app Y) ≫
        E'.rightDerivedPlusSingleUnit (L.obj Y) := by
  have hh := rightDerivedBaseChange_single_unit
    (G := E) (G' := E') (β := L) (γ := 𝟭 D) ((Functor.rightUnitor E).hom ≫ τ) Y
  have hn := (mapDerivedCategoryPlusIdIso D).inv.naturality (E.rightDerivedPlusSingleUnit Y)
  simp only [Functor.id_map] at hn
  unfold coordinateSectionTransport
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app,
    isoWhiskerLeft_inv, whiskerLeft_app, Category.id_comp, Category.assoc]
  erw [reassoc_of% hn, hh, coordinate_id_single,
    Iso.inv_hom_id_app_assoc]
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app]
  erw [Category.id_comp]

/-- Degree-zero homology of normalized section transport respects the augmentations.
Source: Stacks Tag 05TD.
Proof: take H0 of the preceding single-complex equation. The single/H0 isomorphism
is natural in the underived map. The proved single-unit homology comparison
identifies both augmentations with their classical degree-zero versions.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateSectionTransport_zero_unit
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E')
    (Y : C) :
    E.toRightDerivedZero.app Y ≫
        (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).inv ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          ((coordinateSectionTransport L E E' τ).app
            ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≫
              E'.rightDerivedFunctorPlus.map
                ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y)) =
      τ.app Y ≫ E'.toRightDerivedZero.app (L.obj Y) ≫
        (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).inv := by
  have hu := congrArg (fun z ↦ z ≫
      (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).inv)
    (rightDerivedPlusSingleUnitHomology_comp_comparison E Y)
  have hu' := congrArg (fun z ↦ z ≫
      (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).inv)
    (rightDerivedPlusSingleUnitHomology_comp_comparison E' (L.obj Y))
  change (E.rightDerivedPlusSingleUnitHomology Y ≫
      (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).hom) ≫
      (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).inv = _ at hu
  change (E'.rightDerivedPlusSingleUnitHomology (L.obj Y) ≫
      (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).hom) ≫
      (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).inv = _ at hu'
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hu hu'
  let H := DerivedCategory.Plus.homologyFunctor D 0
  have hn := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := D) 0).inv.naturality (τ.app Y)
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [← Category.assoc, ← hu, ← hu']
  unfold rightDerivedPlusSingleUnitHomology
  simp only [Functor.map_comp, Category.assoc]
  erw [← H.map_comp_assoc, ← H.map_comp]
  simp only [Category.assoc]
  erw [coordinateSectionTransport_single_unit, H.map_comp, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  rfl

omit [EnoughInjectives C'] in
/-- For an exact functor the single-complex derived augmentation is the inverse
of its exact single comparison, after the canonical exact-derived identification.
Source: Stacks Tag 05TD.
Proof: expand the single-complex augmentation and apply the unit equation defining
the exact-derived comparison. The homotopy-single comparison is precisely the
exact single comparison by `single_exact_transport`.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateExact_single_unit
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (X : C) :
    L.rightDerivedPlusSingleUnit X ≫
      L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
    (L.mapDerivedCategoryPlusSingleFunctor 0).inv.app X := by
  have ht := single_exact_transport L X
  simp only [singleTransport_hom, Functor.map_id, Category.id_comp,
    Category.comp_id, single_comparison] at ht
  have hf := congr_app L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac
    ((HomotopyCategory.Plus.singleFunctor C 0).obj X)
  simp only [NatTrans.comp_app, whiskerLeft_app] at hf
  apply (cancel_mono ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app X)).1
  erw [Iso.inv_hom_id_app]
  simp only [Category.assoc]
  change ((L.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 X).inv ≫
    L.rightDerivedFunctorPlusUnith.app _ ≫ L.rightDerivedFunctorPlus.map
      (singleTransport C X).hom) ≫ _ ≫ _ = _
  rw [singleTransport_hom, Functor.map_id]
  erw [Category.comp_id]
  simp only [Category.assoc]
  erw [reassoc_of% hf, ht]
  erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
  rfl

omit [EnoughInjectives C'] in
/-- The exact single-complex augmentation is natural in its coefficient object.
Source: Stacks Tag 05TD.
Proof: postcompose by the exact-derived comparison, use its naturality and the
preceding single-unit formula, then apply naturality of the exact single comparison.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateExact_single_unit_naturality
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {X Y : C} (b : X ⟶ Y) :
    (DerivedCategory.Plus.singleFunctor C' 0).map (L.map b) ≫
      L.rightDerivedPlusSingleUnit Y =
    L.rightDerivedPlusSingleUnit X ≫ L.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor C 0).map b) := by
  apply (cancel_mono (L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
    ((DerivedCategory.Plus.singleFunctor C 0).obj Y))).1
  have hn := L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality
    ((DerivedCategory.Plus.singleFunctor C 0).map b)
  simp only [Category.assoc]
  erw [coordinateExact_single_unit, hn, ← Category.assoc, coordinateExact_single_unit]
  exact (L.mapDerivedCategoryPlusSingleFunctor 0).inv.naturality b

/-- Normalized section transport is compatible with composition of right-derived functors.
Source: Stacks Tag 05TD, uniqueness of right-derived transformations.
Proof: use the proved composition equation for raw derived base change. Precompose
it with the inverse comparison for the derived identity. Naturality moves this
inverse through the source composition comparison; the remaining factors are
exactly the two normalized section transports.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateSectionTransport_comp
    {B M B' M' : Type*} [Category* B] [Category* M] [Category* B'] [Category* M']
    [Abelian B] [Abelian M] [Abelian B'] [Abelian M']
    [HasDerivedCategory B] [HasDerivedCategory M]
    [HasDerivedCategory B'] [HasDerivedCategory M']
    [EnoughInjectives B] [EnoughInjectives M]
    [EnoughInjectives B'] [EnoughInjectives M']
    (J : B ⥤ M) (J' : B' ⥤ M') (E : M ⥤ D) (E' : M' ⥤ D)
    (H : B ⥤ D) (H' : B' ⥤ D)
    [J.Additive] [J'.Additive] [E.Additive] [E'.Additive] [H.Additive] [H'.Additive]
    [J.PreservesInjectiveObjects] [J'.PreservesInjectiveObjects]
    (L : B ⥤ B') (N : M ⥤ M') [L.Additive] [N.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (c : J ⋙ E ≅ H) (c' : J' ⋙ E' ≅ H')
    (j : J ⋙ N ⟶ L ⋙ J') (s : E ⟶ N ⋙ E') (t : H ⟶ L ⋙ H')
    (h : ∀ X, c.inv.app X ≫ s.app (J.obj X) ≫ E'.map (j.app X) =
      t.app X ≫ c'.inv.app (L.obj X)) (K : DerivedCategory.Plus B) :
    (rightDerivedFunctorPlusCompIso' J E c).inv.app K ≫
        (coordinateSectionTransport N E E' s).app (J.rightDerivedFunctorPlus.obj K) ≫
        E'.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusBaseChange j).app K) =
      (coordinateSectionTransport L H H' t).app K ≫
        (rightDerivedFunctorPlusCompIso' J' E' c').inv.app
          (L.mapDerivedCategoryPlus.obj K) := by
  have h0 : ∀ X,
      (𝟭 D).map (c.inv.app X) ≫
          ((Functor.rightUnitor E).hom ≫ s).app (J.obj X) ≫ E'.map (j.app X) =
        ((Functor.rightUnitor H).hom ≫ t).app X ≫ c'.inv.app (L.obj X) := by
    intro X
    simp only [Functor.id_map, NatTrans.comp_app, Functor.rightUnitor_hom_app]
    erw [Category.id_comp, Category.id_comp]
    exact h X
  have hh := rightDerivedFunctorPlusBaseChange_comp c c' j
    ((Functor.rightUnitor E).hom ≫ s) ((Functor.rightUnitor H).hom ≫ t) h0 K
  have hn := (Functor.mapDerivedCategoryPlusIdIso D).inv.naturality
    ((rightDerivedFunctorPlusCompIso' J E c).inv.app K)
  simp only [Functor.id_map] at hn
  have he := congrArg (fun z ↦ (Functor.mapDerivedCategoryPlusIdIso D).inv.app
      (H.rightDerivedFunctorPlus.obj K) ≫ z) hh
  erw [← reassoc_of% hn] at he
  simpa only [coordinateSectionTransport, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc] using he

/-- On single complexes, the composition transport square is expressed using
only the canonical single augmentations.
Source: Stacks Tag 05TD.
Proof: conjugate the composition equation by its two comparison isomorphisms.
Naturality moves the source single augmentation through section transport and the
target exact-single comparison through the composition isomorphism. The derived
base-change single-unit equation identifies the remaining three factors.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateSectionTransport_comp_single
    {B M B' M' : Type*} [Category* B] [Category* M] [Category* B'] [Category* M']
    [Abelian B] [Abelian M] [Abelian B'] [Abelian M']
    [HasDerivedCategory B] [HasDerivedCategory M]
    [HasDerivedCategory B'] [HasDerivedCategory M']
    [EnoughInjectives B] [EnoughInjectives M]
    [EnoughInjectives B'] [EnoughInjectives M']
    (J : B ⥤ M) (J' : B' ⥤ M') (E : M ⥤ D) (E' : M' ⥤ D)
    (H : B ⥤ D) (H' : B' ⥤ D)
    [J.Additive] [J'.Additive] [E.Additive] [E'.Additive] [H.Additive] [H'.Additive]
    [J.PreservesInjectiveObjects] [J'.PreservesInjectiveObjects]
    (L : B ⥤ B') (N : M ⥤ M') [L.Additive] [N.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (c : J ⋙ E ≅ H) (c' : J' ⋙ E' ≅ H')
    (j : J ⋙ N ⟶ L ⋙ J') (s : E ⟶ N ⋙ E') (t : H ⟶ L ⋙ H')
    (h : ∀ X, c.inv.app X ≫ s.app (J.obj X) ≫ E'.map (j.app X) =
      t.app X ≫ c'.inv.app (L.obj X)) (F : B) :
    E.rightDerivedFunctorPlus.map (J.rightDerivedPlusSingleUnit F) ≫
        (rightDerivedFunctorPlusCompIso' J E c).hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj F) ≫
        (coordinateSectionTransport L H H' t).app
          ((DerivedCategory.Plus.singleFunctor B 0).obj F) ≫
        H'.rightDerivedFunctorPlus.map
          ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app F) =
      (coordinateSectionTransport N E E' s).app
          ((DerivedCategory.Plus.singleFunctor M 0).obj (J.obj F)) ≫
        E'.rightDerivedFunctorPlus.map
          ((N.mapDerivedCategoryPlusSingleFunctor 0).hom.app (J.obj F) ≫
            (DerivedCategory.Plus.singleFunctor M' 0).map (j.app F) ≫
            J'.rightDerivedPlusSingleUnit (L.obj F)) ≫
        (rightDerivedFunctorPlusCompIso' J' E' c').hom.app
          ((DerivedCategory.Plus.singleFunctor B' 0).obj (L.obj F)) := by
  let K := (DerivedCategory.Plus.singleFunctor B 0).obj F
  let C₀ := rightDerivedFunctorPlusCompIso' J E c
  let C₁ := rightDerivedFunctorPlusCompIso' J' E' c'
  let η := coordinateSectionTransport N E E' s
  have hc := coordinateSectionTransport_comp J J' E E' H H' L N c c' j s t h K
  have hc' := congrArg (fun z ↦ C₀.hom.app K ≫ z ≫
    C₁.hom.app (L.mapDerivedCategoryPlus.obj K)) hc
  have hc'' : C₀.hom.app K ≫ (coordinateSectionTransport L H H' t).app K =
      η.app (J.rightDerivedFunctorPlus.obj K) ≫
        E'.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusBaseChange j).app K) ≫
        C₁.hom.app (L.mapDerivedCategoryPlus.obj K) := by
    simp only [C₀, C₁, Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app] at hc'
    erw [Category.comp_id] at hc'
    exact hc'.symm
  have hn := C₁.hom.naturality ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  have hη := η.naturality (J.rightDerivedPlusSingleUnit F)
  have hu := rightDerivedBaseChange_single_unit j F
  simp only [Functor.comp_map] at hn hη
  change E.rightDerivedFunctorPlus.map (J.rightDerivedPlusSingleUnit F) ≫
    C₀.hom.app K ≫ (coordinateSectionTransport L H H' t).app K ≫ _ = _
  erw [reassoc_of% hc'', ← hn, reassoc_of% hη]
  erw [← E'.rightDerivedFunctorPlus.map_comp_assoc,
    ← E'.rightDerivedFunctorPlus.map_comp_assoc]
  simp only [Category.assoc]
  erw [hu]
  rfl


/-- The single-complex composition square remains natural after inverting the two
open coefficient comparisons and inserting the ambient coefficient map.
Source: Stacks Tag 05TD, and functoriality of localization.
Proof: precompose the single composition equation by the inverse source coefficient
map and postcompose by the target coefficient map. Naturality of normalized transport,
the exact single comparison and the target single augmentation move these maps to
the underived coefficient square. Cancel the two coefficient isomorphisms in that
square and apply the single functor. Functoriality finishes the calculation.
(blueprint: aux-lem-pur-coordinate-derived-transport-normalization). -/
theorem coordinateSectionTransport_comp_coefficients
    {B M B' M' : Type*} [Category* B] [Category* M] [Category* B'] [Category* M']
    [Abelian B] [Abelian M] [Abelian B'] [Abelian M']
    [HasDerivedCategory B] [HasDerivedCategory M]
    [HasDerivedCategory B'] [HasDerivedCategory M']
    [EnoughInjectives B] [EnoughInjectives M]
    [EnoughInjectives B'] [EnoughInjectives M']
    (J : B ⥤ M) (J' : B' ⥤ M') (E : M ⥤ D) (E' : M' ⥤ D)
    (H : B ⥤ D) (H' : B' ⥤ D)
    [J.Additive] [J'.Additive] [E.Additive] [E'.Additive] [H.Additive] [H'.Additive]
    [J.PreservesInjectiveObjects] [J'.PreservesInjectiveObjects]
    (L : B ⥤ B') (N : M ⥤ M') [L.Additive] [N.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (c : J ⋙ E ≅ H) (c' : J' ⋙ E' ≅ H')
    (j : J ⋙ N ⟶ L ⋙ J') (s : E ⟶ N ⋙ E') (t : H ⟶ L ⋙ H')
    (h : ∀ X, c.inv.app X ≫ s.app (J.obj X) ≫ E'.map (j.app X) =
      t.app X ≫ c'.inv.app (L.obj X))
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (F : B) (F' : B') (U : M) (U' : M')
    (b : L.obj F ⟶ F') (d : N.obj U ⟶ U')
    (z : J.obj F ⟶ U) (z' : J'.obj F' ⟶ U') [IsIso z] [IsIso z']
    (hz : j.app F ≫ J'.map b ≫ z' = N.map z ≫ d) :
    E.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor M 0).map (CategoryTheory.inv z) ≫
            J.rightDerivedPlusSingleUnit F) ≫
        (rightDerivedFunctorPlusCompIso' J E c).hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj F) ≫
        (coordinateSectionTransport L H H' t).app
          ((DerivedCategory.Plus.singleFunctor B 0).obj F) ≫
        H'.rightDerivedFunctorPlus.map
          ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
            (DerivedCategory.Plus.singleFunctor B' 0).map b) =
      (coordinateSectionTransport N E E' s).app
          ((DerivedCategory.Plus.singleFunctor M 0).obj U) ≫
        E'.rightDerivedFunctorPlus.map
          ((N.mapDerivedCategoryPlusSingleFunctor 0).hom.app U ≫
            (DerivedCategory.Plus.singleFunctor M' 0).map d) ≫
        E'.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor M' 0).map (CategoryTheory.inv z') ≫
            J'.rightDerivedPlusSingleUnit F') ≫
        (rightDerivedFunctorPlusCompIso' J' E' c').hom.app
          ((DerivedCategory.Plus.singleFunctor B' 0).obj F') := by
  let SM := DerivedCategory.Plus.singleFunctor M 0
  let SB' := DerivedCategory.Plus.singleFunctor B' 0
  let SM' := DerivedCategory.Plus.singleFunctor M' 0
  let η := coordinateSectionTransport N E E' s
  let C₁ := rightDerivedFunctorPlusCompIso' J' E' c'
  have hz₀ : N.map (CategoryTheory.inv z) ≫ j.app F ≫ J'.map b =
      d ≫ CategoryTheory.inv z' := by
    apply (cancel_mono z').1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    erw [hz, ← N.map_comp_assoc, IsIso.inv_hom_id, N.map_id, Category.id_comp]
  have hη := η.naturality (SM.map (CategoryTheory.inv z))
  have hn := (N.mapDerivedCategoryPlusSingleFunctor 0).hom.naturality
    (CategoryTheory.inv z)
  have hu := coordinateExact_single_unit_naturality J' b
  have hd : N.mapDerivedCategoryPlus.map (SM.map (CategoryTheory.inv z)) ≫
      (N.mapDerivedCategoryPlusSingleFunctor 0).hom.app (J.obj F) ≫
      SM'.map (j.app F) ≫ J'.rightDerivedPlusSingleUnit (L.obj F) ≫
      J'.rightDerivedFunctorPlus.map (SB'.map b) =
    (N.mapDerivedCategoryPlusSingleFunctor 0).hom.app U ≫
      SM'.map d ≫ SM'.map (CategoryTheory.inv z') ≫
      J'.rightDerivedPlusSingleUnit F' := by
    erw [reassoc_of% hn, ← hu]
    erw [← SM'.map_comp_assoc, ← SM'.map_comp_assoc]
    simp only [Category.assoc]
    erw [hz₀, SM'.map_comp]
    simp only [Category.assoc]
  have hh := congrArg (fun q ↦ E.rightDerivedFunctorPlus.map
      (SM.map (CategoryTheory.inv z)) ≫ q ≫ H'.rightDerivedFunctorPlus.map (SB'.map b))
    (coordinateSectionTransport_comp_single J J' E E' H H' L N c c' j s t h F)
  have hc := C₁.hom.naturality (SB'.map b)
  simp only [Functor.comp_map] at hη hc
  simp only [Functor.map_comp, Category.assoc] at hh ⊢
  erw [← hc, reassoc_of% hη] at hh
  simp only [← E'.rightDerivedFunctorPlus.map_comp_assoc] at hh
  erw [hd] at hh
  simpa only [E'.rightDerivedFunctorPlus.map_comp, Category.assoc] using hh


end CategoryTheory.Functor
