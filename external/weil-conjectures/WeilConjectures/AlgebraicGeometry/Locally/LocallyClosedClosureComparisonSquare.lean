/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement
import WeilConjectures.AlgebraicGeometry.Derived.DerivedImmersionComparisonNormalization

/-! # The normalized locally closed closure comparison square

All composites below use the specified open comparison and the specified derived
closed counit mate. Normalized closure identifications are expressed in derived
coordinates: their restriction is the identity under the actual open units, closed
counits and pullback compositors. This normalization also characterizes the
termwise identifications uniquely, so it does not permit a different choice of map.

## References

* Stacks Tags 0GJ1, 04CA, 09AF, 099R and 0B65
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 2048

universe u uC uD vC vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale
/-- The closed-then-open extension F_e on the bounded below derived category. -/
abbrev closureSquareEtaleFactor (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus ⋙
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus

/-- The closed-then-open extension F_p on the bounded below derived category. -/
abbrev closureSquareProEtaleFactor (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus ⋙
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus

/-- The termwise canonical open comparison o_j, with its direction fixed. -/
def closureSquareOpenComparison (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
        siteComparisonDerivedPullbackPlus X A ≅
      siteComparisonDerivedPullbackPlus U A ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical pullback compositor for a specified factorization of s. -/
def closureSquareEtalePullComp (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (f : S ⟶ V) (g : V ⟶ T) (s : S ⟶ T)
    (h : f ≫ g = s) :
    (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus :=
  Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} A) f g s h.symm

/-- The inverse open unit on D+, descended termwise from the sheaf unit. -/
def closureSquareProEtaleOpenRestriction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit).symm ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- The canonical pullback compositor for a specified factorization of s. -/
def closureSquareProEtalePullComp (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (f : S ⟶ V) (g : V ⟶ T) (s : S ⟶ T)
    (h : f ≫ g = s) :
    (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusNatIso
      (upperStarCongr (ModuleCat.{u + 1} A) h.symm ≪≫
        upperStarComp (ModuleCat.{u + 1} A) f g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem closure_upper_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app F) ≫
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j).inv.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ≫
    (upperStar (ModuleCat.{u + 1} A) j).map
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).hom.app F) =
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) := by
  have h := (openComparison_unit_normalization A j).2 F
  change _ ≫ (openComparisonRestrictionIso A j).hom.app _ ≫ _ = _ at h
  simp only [openComparisonRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  let B := ModuleCat.{u + 1} A
  have he : (Etale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app F =
      (Etale.openImmersionLowerShriekAdjunction B j).unit.app F ≫
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv.app
        ((Etale.openImmersionLowerShriek B j).obj F) := rfl
  have hp : (openImmersionLowerShriekUpperStarAdjunction B j).unit.app
      ((comparisonUpperStar B U).obj F) =
      (openImmersionLowerShriekAdjunction B j).unit.app
        ((comparisonUpperStar B U).obj F) ≫
      (upperStarIsoOpenImmersionRestriction B j).inv.app _ := rfl
  rw [he, hp, Functor.map_comp]
  rw [← cancel_mono ((upperStarIsoOpenImmersionRestriction B j).hom.app _)]
  dsimp only [B, Functor.comp_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hn := (upperStarIsoOpenImmersionRestriction B j).hom.naturality
    ((openImmersionLowerShriekComparisonUpperStarIso B j).hom.app F)
  dsimp only [B, Functor.comp_obj] at hn
  erw [hn]
  exact h
set_option backward.isDefEq.respectTransparency false in
private theorem closure_derived_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    let a := (comparisonUpperStarCompUpperStarIso B j).symm
    let e := openImmersionLowerShriekComparisonUpperStarIso B j
    (comparisonUpperStar B U).mapDerivedCategory.map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction.unit.app
          K) ≫
    (Functor.mapDerivedCategorySquareIso a).hom.app
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.obj K) ≫
    (upperStar B j).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso e).hom.app K) =
    (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction.unit.app
      ((comparisonUpperStar B U).mapDerivedCategory.obj K) := by
  dsimp only
  let B := ModuleCat.{u + 1} A
  let e := openImmersionLowerShriekComparisonUpperStarIso B j
  let a := (comparisonUpperStarCompUpperStarIso B j).symm
  have hu : ∀ F,
      (openImmersionLowerShriekUpperStarAdjunction B j).unit.app
          ((comparisonUpperStar B U).obj F) ≫
        (upperStar B j).map (e.inv.app F) =
      (comparisonUpperStar B U).map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app F) ≫
        a.hom.app ((Etale.openImmersionLowerShriek B j).obj F) := by
    intro F
    rw [← closure_upper_unit A j F]
    dsimp only [B, e, a]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (Etale.openImmersionLowerShriekUpperStarAdjunction B j)
    (openImmersionLowerShriekUpperStarAdjunction B j) a e.symm hu K
  have hs : Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs] at h
  dsimp only [B, e, a] at h
  rw [← reassoc_of% h, ← Functor.map_comp]
  simp only [Iso.symm_hom, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
private theorem closure_inclusion_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem closure_inclusion_comp_inv {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K)).inv =
      ((Functor.mapDerivedCategoryCompIso F G).symm.app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K

set_option backward.isDefEq.respectTransparency false in
private theorem closure_plus_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    (comparisonUpperStar B U).mapDerivedCategoryPlus.map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction
        B j).mapDerivedCategoryPlusAdjunction.unit.app K) ≫
    (fixedComparisonPullbackPlus A j).hom.app
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategoryPlus.obj K) ≫
    (upperStar B j).mapDerivedCategoryPlus.map
      ((closureSquareOpenComparison A j).hom.app K) =
    (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryPlusAdjunction.unit.app
      ((comparisonUpperStar B U).mapDerivedCategoryPlus.obj K) := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := closure_derived_unit A j K.obj
  simp only [Functor.map_comp, closure_inclusion_map,
    fixedComparisonPullbackPlus, closureSquareOpenComparison, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, closure_inclusion_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app] at h ⊢
  repeat erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [Category.comp_id, Functor.comp_obj, Functor.mapDerivedCategoryPlus,
    ObjectProperty.lift, DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor,
    Functor.id_obj] using h

set_option backward.isDefEq.respectTransparency false in
private theorem closure_descent_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Functor.mapDerivedCategoryPlusNatIso e.symm).hom =
      (Functor.mapDerivedCategoryPlusNatIso e).inv := by
  apply NatTrans.ext
  funext X
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.mapDerivedCategoryNatIso_symm]
  have h : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusNatIso e).app X) =
      (Functor.mapDerivedCategoryNatIso e).app X.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app e X)
  exact (congrArg Iso.inv h).symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

-- The descended ordinary unit is the unit of the exact derived adjunction.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closure_pullback_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (f : S ⟶ V) (g : V ⟶ T) (s : S ⟶ T)
    (h : f ≫ g = s)
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (fixedComparisonPullbackPlus A s).hom.app L ≫
        (closureSquareProEtalePullComp A f g s h).hom.app
          ((siteComparisonDerivedPullbackPlus T A).obj L) =
      (siteComparisonDerivedPullbackPlus S A).map
          ((closureSquareEtalePullComp A f g s h).hom.app L) ≫
        (fixedComparisonPullbackPlus A f).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj L) ≫
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus A g).hom.app L) := by
  subst s
  let B := ModuleCat.{u + 1} A
  have hs (M : Sheaf T.smallEtaleTopology B) :=
    ((supportSiteComparison_pullback_coherent.{u}).2.2 A).2.1 S V T f g M
  have hq (M : Sheaf T.smallEtaleTopology B) :
      (comparisonUpperStarCompUpperStarIso B (f ≫ g)).hom.app M ≫
          (comparisonUpperStar B S).map ((Etale.upperStarComp B f g).hom.app M) =
        (upperStarComp B f g).hom.app ((comparisonUpperStar B T).obj M) ≫
          (upperStar B f).map ((comparisonUpperStarCompUpperStarIso B g).hom.app M) ≫
          (comparisonUpperStarCompUpperStarIso B f).hom.app
            ((Etale.upperStar B g).obj M) := by
    have hm := hs M
    have hec : etaleComparisonComp B f g = Etale.upperStarComp B f g := by
      unfold etaleComparisonComp Etale.upperStarComp
      rfl
    have hpc : proEtaleComparisonComp B f g = upperStarComp B f g := by
      unfold proEtaleComparisonComp upperStarComp
      rfl
    rw [hec, hpc] at hm
    change (comparisonUpperStar B S).map ((Etale.upperStarComp B f g).hom.app M) ≫
        (comparisonUpperStarCompUpperStarIso B f).inv.app ((Etale.upperStar B g).obj M) ≫
        (upperStar B f).map ((comparisonUpperStarCompUpperStarIso B g).inv.app M) =
      (comparisonUpperStarCompUpperStarIso B (f ≫ g)).inv.app M ≫
        (upperStarComp B f g).hom.app ((comparisonUpperStar B T).obj M) at hm
    apply (cancel_epi ((comparisonUpperStarCompUpperStarIso B (f ≫ g)).inv.app M)).1
    rw [Iso.inv_hom_id_app_assoc, ← reassoc_of% hm,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
  have hd := Functor.mapDerivedCategoryPlusSquareIso_comp
    (Etale.upperStar B g) (Etale.upperStar B f) (Etale.upperStar B (f ≫ g))
    (upperStar B g) (upperStar B f) (upperStar B (f ≫ g))
    (comparisonUpperStar B T) (comparisonUpperStar B V) (comparisonUpperStar B S)
    (comparisonUpperStarCompUpperStarIso B g) (comparisonUpperStarCompUpperStarIso B f)
    (comparisonUpperStarCompUpperStarIso B (f ≫ g))
    (Etale.upperStarComp B f g) (upperStarComp B f g) hq L
  have hi {X Y : Scheme.{u}} (k : X ⟶ Y) :
      (Functor.mapDerivedCategoryPlusSquareIso (comparisonUpperStar B Y) (upperStar B k)
        (Etale.upperStar B k) (comparisonUpperStar B X)
        (comparisonUpperStarCompUpperStarIso B k)).hom =
      (fixedComparisonPullbackPlus A k).inv := by
    have hs :
        (Functor.mapDerivedCategoryPlusNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) k).symm).inv =
        (Functor.mapDerivedCategoryPlusNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) k)).hom :=
      (closure_descent_symm
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) k).symm).symm
    dsimp only [B]
    simp only [Functor.mapDerivedCategoryPlusSquareIso, fixedComparisonPullbackPlus,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
    rw [hs]
  rw [hi, hi, hi] at hd
  change (fixedComparisonPullbackPlus A (f ≫ g)).inv.app L ≫
      (siteComparisonDerivedPullbackPlus S A).map
        ((closureSquareEtalePullComp A f g (f ≫ g) rfl).hom.app L) =
    (closureSquareProEtalePullComp A f g (f ≫ g) rfl).hom.app
      ((siteComparisonDerivedPullbackPlus T A).obj L) ≫
      (upperStar B f).mapDerivedCategoryPlus.map
        ((fixedComparisonPullbackPlus A g).inv.app L) ≫
      (fixedComparisonPullbackPlus A f).inv.app
        ((Etale.upperStar B g).mapDerivedCategoryPlus.obj L) at hd
  dsimp only [B] at hd
  apply (cancel_epi ((fixedComparisonPullbackPlus A (f ≫ g)).inv.app L)).1
  rw [Iso.inv_hom_id_app_assoc, reassoc_of% hd,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

-- Pasting two restriction-normalized comparison squares preserves normalization.
end AlgebraicGeometry.ProEtale
