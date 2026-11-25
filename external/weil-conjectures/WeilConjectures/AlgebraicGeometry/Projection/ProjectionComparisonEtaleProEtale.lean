/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Topology.Stratification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option linter.privateModule false

/-!
# Etale-to-pro-etale comparison of the direct-image projection morphism

The two routes are components of a single natural transformation on the full
subcategory of admissible pairs. This records both their equality and its
naturality, including arbitrary morphisms in both inputs. All operations are
ordinary uncompleted constant-coefficient operations.

## References

* Stacks Project, Tags 09A6, 07A4 and 0E48
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

open CategoryTheory.Functor

private lemma normalize_counit_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F F0 : D ⥤ C) (G G0 : D' ⥤ C') (N : D ⥤ D') (M : C ⥤ C')
    (ie : F ≅ F0) (ip : G ≅ G0) (a : F ⋙ M ≅ N ⋙ G)
    (s : F0 ⋙ M ≅ N ⋙ G0)
    (ht : ∀ Z : D, s.hom.app Z ≫ ip.inv.app (N.obj Z) =
      M.map (ie.inv.app Z) ≫ a.hom.app Z)
    {K : C} {Z W : D} {T : D'} (c : Z ≅ W) (b : N.obj Z ⟶ T)
    (eps : F.obj W ⟶ K) (eps' : G.obj T ⟶ M.obj K)
    (h : s.hom.app Z ≫ G0.map b ≫ ip.inv.app T ≫ eps' =
      M.map (F0.map c.hom) ≫ M.map (ie.inv.app W) ≫ M.map eps) :
    a.inv.app W ≫ M.map eps = G.map (N.map c.inv ≫ b) ≫ eps' := by
  rw [ip.inv.naturality_assoc, reassoc_of% (ht Z)] at h
  rw [← M.map_comp_assoc, ie.inv.naturality, M.map_comp, Category.assoc] at h
  have hh := (cancel_epi (M.map (ie.inv.app Z))).1 h
  rw [← cancel_epi (a.hom.app W), Iso.hom_inv_id_app_assoc]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := a.hom.naturality c.inv
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hh]
  rw [← M.map_comp_assoc, ← F.map_comp, c.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

namespace AlgebraicGeometry.ProEtale

private lemma map_plus_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K.obj := by
  exact congrArg Iso.inv (show DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K) =
      ((Functor.mapDerivedCategoryCompIso F G).symm).app K.obj from
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K))

private lemma included_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((fixedComparisonPullbackPlus A p).hom.app K) =
      (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p).symm).hom.app
          K.obj := by
  simp only [fixedComparisonPullbackPlus, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, map_plus_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.mapDerivedCategorySquareIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma comparison_direct_image_eq_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (comparisonOpenDerivedPullbackIso A p).inv).app K.obj =
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
    DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K) := by
  apply ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, mateEquiv_counit, Functor.map_comp, Category.assoc]
  have h := congrArg DerivedCategory.Plus.ι.map
    (fixedComparisonDirectImageMatePlus_counit A p K)
  have he : DerivedCategory.Plus.ι.map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p).counit.app K) =
      (Etale.upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).ofNatIsoLeft
        (Etale.upperStar (ModuleCat A) p).leftDerivedFunctorIsoMapDerivedCategory).counit.app
          K.obj := by
    unfold Etale.derivedUpperStarLowerStarAdjunctionPlus Adjunction.derivedAdjunctionPlus
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
    rfl
  have hp : DerivedCategory.Plus.ι.map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K)) =
      (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K)) ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).ofNatIsoLeft
        (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctorIsoMapDerivedCategory).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj) := by
    unfold derivedUpperStarLowerStarAdjunctionPlus Adjunction.derivedAdjunctionPlus
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
    rfl
  simp only [Functor.map_comp] at h
  change _ ≫ (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
    (DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K)) ≫ _ =
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} A) p).counit.app K)) at h
  rw [he, hp] at h
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp] at h
  let Fe := Etale.upperStar (ModuleCat.{u + 1} A) p
  let Fp := upperStar (ModuleCat.{u + 1} A) p
  let FX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let FY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let ie := Fe.leftDerivedFunctorIsoMapDerivedCategory
  let ip := Fp.leftDerivedFunctorIsoMapDerivedCategory
  let a := comparisonOpenDerivedPullbackIso A p
  have ht (Z : Etale.DerivedCategoryModule A Y) :
      (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p).symm).hom.app Z ≫
        ip.inv.app (FY.obj Z) = FX.map (ie.inv.app Z) ≫ a.hom.app Z := by
    simp only [a, comparisonOpenDerivedPullbackIso, supportComparison_eq,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Etale.leftDerivedUpperStarIsoMapDerivedCategory, ie, Fe, FX, Category.assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [ip, Fp, FY, leftDerivedUpperStarIsoMapDerivedCategory]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [included_pullback] at h
  let sq := Functor.mapDerivedCategorySquareIso
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p).symm
  let c := (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app K
  let bb := DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K)
  have hh := normalize_counit_square Fe.leftDerivedFunctor Fe.mapDerivedCategory
    Fp.leftDerivedFunctor Fp.mapDerivedCategory FY FX ie ip a sq ht c bb
    ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.app K.obj)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.app (FX.obj K.obj))
    (by
      simp only [bb, CategoryTheory.Functor.map_comp, Category.assoc]
      exact h)
  simp only [bb, CategoryTheory.Functor.map_comp, Category.assoc] at hh
  exact hh

private lemma comparison_direct_image_inclusion
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.inv.app
      ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) p).obj K) ≫
    DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.hom.app
        K) =
    (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (comparisonOpenDerivedPullbackIso A p).inv).app K.obj := by
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact (comparison_direct_image_eq_mate A p K).symm

end AlgebraicGeometry.ProEtale
