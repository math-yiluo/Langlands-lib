/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Composition of ordinary direct-image site boundaries

Source: the ordered exterior-product and comparison paragraphs of
sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar upperStar Etale.lowerStar Etale.upperStar

/-- Ordinary direct-image boundary, with the output in the bounded-below etale category. -/
def ordinaryBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory) ⋙
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor ≅
    (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus ⋙
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) :=
  rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} A) f ≪≫
    Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.symm _

private theorem boundary_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    have := isIso_comparisonDirectImagePlus A f
    (ordinaryBoundary A f).hom.app K =
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K) ≫
      DerivedCategory.Plus.ι.map ((asIso (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A)))).inv.app K) := by
  simp only [ordinaryBoundary, rightDerivedLowerStarComparisonIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryPlusCompatibility,
    Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

private theorem comparison_inverse_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    have := isIso_comparisonDirectImagePlus A f
    have := isIso_comparisonDirectImagePlus A g
    have := isIso_comparisonDirectImagePlus A (f ≫ g)
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus.map
        ((asIso (Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A)))).inv.app K) ≫
      (asIso (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} A)))).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
        ((etaleComparisonDirectImageCompIso A f g).hom.app K) =
    (proEtaleComparisonDirectImageCompIso A f g).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K) ≫
      (asIso (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} A)))).inv.app K := by
  have := isIso_comparisonDirectImagePlus A f
  have := isIso_comparisonDirectImagePlus A g
  have := isIso_comparisonDirectImagePlus A (f ≫ g)
  apply (cancel_mono ((asIso (Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} A)))).hom.app K)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have hf := comparisonDirectImagePlus_comp A f g K
  change _ ≫ (asIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} A)))).hom.app K =
    (asIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} A)))).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus.map
        ((asIso (Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A)))).hom.app K) ≫ _ at hf
  rw [hf]
  erw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Composition of ordinary direct-image site boundaries.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered composition and comparison;
parent proof Step 3 (blueprint: lem-pur-ordinary-boundary-composition).

Proof: Expand each boundary as the inverse pro-etale inclusion map followed by inclusion of the
inverse bounded direct-image mate. Naturality moves that mate through the next inclusion map.
The inverse of comparisonDirectImagePlus_comp then composes the two bounded mates. Finally
generic right-derived composition compatibility with D+ cancels the intermediate inclusion
maps. Cancelling the final mate and inclusion isomorphisms gives exactly this equation. -/
theorem ordinaryBoundary_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
        ((ordinaryBoundary A f).hom.app K) ≫
      (ordinaryBoundary A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory).map
        ((etaleComparisonDirectImageCompIso A f g).hom.app K) =
    (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
      (lowerStar (ModuleCat.{u + 1} A) g)
      (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj) ≫
      (ordinaryBoundary A (f ≫ g)).hom.app K := by
  have := isIso_comparisonDirectImagePlus A f
  have := isIso_comparisonDirectImagePlus A g
  have := isIso_comparisonDirectImagePlus A (f ≫ g)
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
  rw [boundary_hom, boundary_hom, boundary_hom]
  erw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility.inv.naturality
    ((asIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A)))).inv.app K)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc]
  erw [reassoc_of% hn]
  have hi := comparison_inverse_comp A f g K
  have hi' := congrArg DerivedCategory.Plus.ι.map hi
  simp only [Functor.map_comp] at hi'
  erw [hi']
  have hc := Etale.right_derived_comp_prime_plus
    (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)
    (lowerStarComp (ModuleCat.{u + 1} A) f g)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K)
  apply (cancel_mono (DerivedCategory.Plus.ι.map
    ((asIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} A)))).hom.app K))).1
  have hih := Iso.inv_hom_id_app (asIso (Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} A)))) K
  have hih' := congrArg DerivedCategory.Plus.ι.map hih
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hih'
  erw [Category.assoc, Category.assoc, Category.assoc, hih', Category.comp_id]
  erw [Category.assoc, Category.assoc, Category.assoc, hih', Category.comp_id]
  apply (cancel_mono
    ((lowerStar (ModuleCat.{u + 1} A) (f ≫ g)).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K))).1
  simp only [Category.assoc]
  erw [hc]
  erw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale
