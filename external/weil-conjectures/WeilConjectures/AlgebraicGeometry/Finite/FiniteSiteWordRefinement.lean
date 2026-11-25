/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement

public import Mathlib.AlgebraicGeometry.Scheme

public import Mathlib.RingTheory.Noetherian.Defs

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison

/-!
# Finite-site words and pushed proper/open refinements

Source: Stacks Project, proetale.tex, Tags 09A6 and 09AF, and more-etale.tex,
Tag 0F7I; blueprint exceptional reduction, Locality paragraph
(blueprint: lem-sp-finite-site-word-refinement).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u uC uD uE uF vC vD vE vF

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

section DerivedTools

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
-- The etale base-change helpers use `Category C`, whose morphism universe equals
-- the object universe. Small-site sheaf categories need independent universes.
-- Each helper states all category binders explicitly to record this generalization.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedNatIso_symm
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlusNatIso,
    Functor.mapDerivedCategoryPlusCompatibility, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso, NatIso.mapHomologicalComplex, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Iso.refl_symm, Iso.refl_trans,
    Functor.fullyFaithfulCancelRight_hom_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.refl_hom, NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.ι_map, Functor.fullyFaithfulCancelRight_inv_app, Iso.trans_inv,
    Iso.refl_inv, Functor.isoWhiskerLeft_inv, Category.id_comp]
  congr 2
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedSquare_symm
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {E : Type uE} {F : Type uF} [Category.{vE} E] [Category.{vF} F] [Abelian E] [Abelian F]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (R : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (S : E ⥤ F)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (q : R ⋙ G ≅ L ⋙ S) :
    Functor.mapDerivedCategoryPlusSquareIso L S R G q.symm =
      (Functor.mapDerivedCategoryPlusSquareIso R G L S q).symm := by
  simp only [Functor.mapDerivedCategoryPlusSquareIso, derivedNatIso_symm]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedComp_symm
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (q : H ≅ F ⋙ G) :
    (Functor.mapDerivedCategoryPlusCompIso F G).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso q.symm =
      (Functor.mapDerivedCategoryPlusNatIso q ≪≫
        Functor.mapDerivedCategoryPlusCompIso F G).symm := by
  simp only [derivedNatIso_symm]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedId_fac
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
    (L : C ⥤ C) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : L ≅ 𝟭 C) (K : HomotopyCategory.Plus C) :
    (Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
    L.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  rw [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem square_identity
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (R : C ⥤ D) (G : D ⥤ D) (L : C ⥤ C)
    [R.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (q : R ⋙ G ≅ L ⋙ R) (eL : L ≅ 𝟭 C) (eG : G ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ R.map (eL.hom.app X) = eG.hom.app (R.obj X))
    (K : DerivedCategory.Plus C) :
    (Functor.mapDerivedCategoryPlusSquareIso R G L R q).hom.app K ≫
      R.mapDerivedCategoryPlus.map ((Functor.mapDerivedCategoryPlusNatIso eL ≪≫
        Functor.mapDerivedCategoryPlusIdIso C).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso eG ≪≫
        Functor.mapDerivedCategoryPlusIdIso D).hom.app (R.mapDerivedCategoryPlus.obj K) := by
  let eLD := Functor.mapDerivedCategoryPlusNatIso eL ≪≫
    Functor.mapDerivedCategoryPlusIdIso C
  let eGD := Functor.mapDerivedCategoryPlusNatIso eG ≪≫
    Functor.mapDerivedCategoryPlusIdIso D
  have hn : (Functor.mapDerivedCategoryPlusSquareIso R G L R q).hom ≫
      Functor.whiskerRight eLD.hom R.mapDerivedCategoryPlus =
      Functor.whiskerLeft R.mapDerivedCategoryPlus eGD.hom := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← cancel_mono (R.mapDerivedCategoryPlusFactorsh.hom.app X)]
    have hnat := eGD.hom.naturality (R.mapDerivedCategoryPlusFactorsh.hom.app X)
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hnat
    rw [Category.assoc, ← hnat]
    dsimp only [eLD, eGD]
    rw [derivedId_fac, derivedId_fac, Functor.map_comp, Category.assoc]
    have hnR := R.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus eL.hom).app X)
    dsimp only [Functor.comp_map] at hnR
    erw [hnR]
    erw [reassoc_of% (Functor.mapDerivedCategoryPlusSquareIso_fac R G L R q X)]
    congr 2
    rw [← DerivedCategory.Plus.Qh.map_comp]
    congr 1
    apply (HomotopyCategory.Plus.ι D).map_injective
    simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    obtain ⟨⟨P⟩, hP⟩ := X
    change (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app P) ≫
      (R.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient C (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eL.hom (.up ℤ)).app P)) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex eG.hom (.up ℤ)).app
          ((R.mapHomologicalComplex (.up ℤ)).obj P))
    rw [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    congr 1
    apply HomologicalComplex.Hom.ext
    funext i
    exact hq (P.X i)
  exact NatTrans.congr_app hn K

end DerivedTools

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The specified finite-site comparison for a proper/open word, with canonical
associators. Source: Stacks Tags 09A6, 09AF and 0F7I
(blueprint: lem-sp-finite-site-word-refinement). -/
def finiteSiteWordComparison (R : Type (u + 1)) [CommRing R]
    {X W V : Scheme.{u}} (j : X ⟶ W) [IsOpenImmersion j] (r : W ⟶ V) :
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus ⋙
      Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) r) ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} R) V).mapDerivedCategoryPlus ⟶
    (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus ⋙
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorPlus) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus
      (fixedComparisonDirectImageMatePlus R r) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (properOpenSiteExtensionIso R j).hom
      (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- The canonical etale pushed-refinement component, with r1 defined as r2 after u.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-site-word-refinement). -/
def finiteSiteEtaleRefinement (R : Type (u + 1)) [CommRing R] [Finite R]
    {X W₁ W₂ V : Scheme.{u}} (j₁ : X ⟶ W₁) (j₂ : X ⟶ W₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (a : W₁ ⟶ W₂) [IsProper a] (r₂ : W₂ ⟶ V) (h : j₁ ≫ a = j₂)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) r₂).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j₂).mapDerivedCategoryPlus.obj
          E) ⟶
      (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) (a ≫ r₂)).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j₁).mapDerivedCategoryPlus.obj
          E) :=
  (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) r₂).map
      (Etale.properOpenComparison R a j₁ j₂ h E) ≫
    (etaleComparisonDirectImageCompIso R a r₂).hom.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j₁).mapDerivedCategoryPlus.obj E)

/-- The canonical pro-etale pushed-refinement component on etale-origin input.
The open-adjunct comparison is the published three-constituent theta comparison.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-site-word-refinement). -/
def finiteSiteProEtaleRefinement (R : Type (u + 1)) [CommRing R] [Finite R]
    {X W₁ W₂ V : Scheme.{u}} (j₁ : X ⟶ W₁) (j₂ : X ⟶ W₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (a : W₁ ⟶ W₂) [IsProper a] (r₂ : W₂ ⟶ V) (h : j₁ ≫ a = j₂)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (lowerStar (ModuleCat.{u + 1} R) r₂).rightDerivedFunctorPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j₂).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) ⟶
      (lowerStar (ModuleCat.{u + 1} R) (a ≫ r₂)).rightDerivedFunctorPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j₁).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) :=
  (lowerStar (ModuleCat.{u + 1} R) r₂).rightDerivedFunctorPlus.map
      (properOpenProEtaleIsoPlus R a j₁ j₂ h E).hom ≫
    (proEtaleComparisonDirectImageCompIso R a r₂).hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j₁).mapDerivedCategoryPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E))

/-- Termwise descent of the canonical Etale open compositor, in the orientation
from iterated to composite extension. Source: Stacks Tags 09AF and 03EH
(blueprint: lem-sp-finite-site-word-refinement). -/
def finiteSiteEtaleOpenComp (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a).mapDerivedCategoryPlus ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) b).mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) (a ≫ b)).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} R)
      a b).symm

/-- Termwise descent of the canonical Etale open unit identification.
Source: Stacks Tags 09AF and 03EH (blueprint: lem-sp-finite-site-word-refinement). -/
def finiteSiteEtaleOpenId (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategoryPlus ≅
      𝟭 _ :=
  Functor.mapDerivedCategoryPlusNatIso
      (Adjunction.leftAdjointIdIso
        (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) (𝟙 X))
        (Etale.upperStarId (ModuleCat.{u + 1} R) X)) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- Termwise descent of the canonical ProEtale open compositor, in the orientation
from iterated to composite extension. Source: Stacks Tags 09AF and 03EH
(blueprint: lem-sp-finite-site-word-refinement). -/
def finiteSiteProEtaleOpenComp (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) a).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) b).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) (a ≫ b)).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (proEtaleOpenExtensionComp R a b).symm

/-- Termwise descent of the canonical ProEtale open unit identification.
Source: Stacks Tags 09AF and 03EH (blueprint: lem-sp-finite-site-word-refinement). -/
def finiteSiteProEtaleOpenId (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategoryPlus ≅
      𝟭 _ :=
  Functor.mapDerivedCategoryPlusNatIso
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} R) X)) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

private theorem siteExtension_symm (R : Type (u + 1)) [CommRing R]
    {X W : Scheme.{u}} (j : X ⟶ W) [IsOpenImmersion j] :
    Functor.mapDerivedCategoryPlusSquareIso
        (comparisonUpperStar (ModuleCat.{u + 1} R) X)
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) j)
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j)
        (comparisonUpperStar (ModuleCat.{u + 1} R) W)
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) j).symm =
      (properOpenSiteExtensionIso R j).symm := by
  exact derivedSquare_symm _ _ _ _ _

private theorem etaleOpenComp_symm (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    finiteSiteEtaleOpenComp R a b =
      (Functor.mapDerivedCategoryPlusNatIso
          (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} R) a b) ≪≫
        Functor.mapDerivedCategoryPlusCompIso
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a)
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) b)).symm := by
  exact derivedComp_symm _ _ _ _

private theorem proEtaleOpenComp_symm (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    finiteSiteProEtaleOpenComp R a b =
      (Functor.mapDerivedCategoryPlusNatIso (proEtaleOpenExtensionComp R a b) ≪≫
        Functor.mapDerivedCategoryPlusCompIso
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) a)
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) b)).symm := by
  exact derivedComp_symm _ _ _ _

/-- Finite-site word comparisons, lower bounds, normalized compositor and unit laws,
and compatibility with pushed proper/open refinements.

Source: Stacks Project, proetale.tex, Tags 09A6 and 09AF; more-etale.tex, Tag 0F7I;
blueprint exceptional reduction, Locality paragraph
(blueprint: lem-sp-finite-site-word-refinement).

Proof (the node's eight steps):
1. Etale and pro-etale extension by zero and comparison inverse image are exact
   (lem-weil-pbc-extension-by-zero-exact, proposition-extension-zero-restriction-closed-subscheme,
   lem-sf-comparison-pullback-exact). The exact-functor cohomology comparison
   (situation-conventions) preserves every specified lower bound.
2. Use enough injectives and an injective representative vanishing below the chosen
   bound (lem-weil-pbc-module-sheaves-enough-injectives,
   lem-weil-pbc-dplus-injective-representative). Direct image computes its right
   derived functor on that representative (lem-weil-pbc-right-derived-plus-injective),
   so every intermediate etale direct image remains bounded below.
3. Apply the canonical sheaf open comparison and its composition law in every degree
   (proposition-comparison-immersions--1, proposition-composition-base-change-rf-shriek--1).
   Naturality makes chain maps; exactness preserves quasi-isomorphisms. Localization
   (lem-weil-pbc-localization-universal-property) descends the maps and equations.
4. Finite affine covers give quasi-compactness; local Noetherianness gives
   quasi-separatedness (lem-weil-pbc-affine-scheme-qcqs,
   lem-weil-pbc-locally-noetherian-quasi-separated). Morphism permanence
   (lem-weil-pbc-qcqs-morphism-permanence) gives qcqs proper maps. The specified mate
   is invertible (lem-weil-pbc-comparison-direct-image-canonical-mate), hence so is B.
   Its domain is exactly the comparison of the bounded-below etale word, the witness.
5. The coherent pullback comparisons (proposition-comparison-etale-derived-category--5) descend
   termwise by exactness (situation-conventions,
   prop-weil-pbc-proetale-constant-exact,
   situation-conventions). Mate pasting
   (lem-weil-pbc-mate-pasting, parts 2 and 3) gives the compositor equation for the
   specified counit mates; adjunction conjugation fixes the canonical compositors.
6. The identity pullback comparison and identity mate law give the proper unit law.
   The open composition law at two identities gives e=e squared; cancellation by
   its inverse gives the open unit law.
7. Expand B and rho. Apply the proper compositor equation, then naturality of d_r2
   at alpha_u and of the pro-etale compositor at e_j1. The three middle factors are
   P_u(e_j1), d_u, and N(alpha_u), all on bounded-below etale inputs from step 2.
8. Substitute the site equation of lem-sp-refinement-coefficient-mate to replace
   those factors by alpha_u_pro after e_j2. Functoriality of P_r2 gives precisely
   rho_pro after B_r2,j2. All constituents are natural, hence so is this equation.
   No Cartesian refinement square, base field, or coefficient presentation is used. -/
theorem finiteSiteWordRefinement (R : Type (u + 1)) [CommRing R] [Finite R] :
    (∀ {X W : Scheme.{u}} [IsNoetherian X] [IsNoetherian W]
      (j : X ⟶ W) [IsOpenImmersion j]
      (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
      (n : ℤ), DerivedCategory.IsGE E.obj n →
      DerivedCategory.IsGE
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus.obj
          E).obj n ∧
      DerivedCategory.IsGE
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E).obj n) ∧
    (∀ {X W : Scheme.{u}} [IsNoetherian X] [IsNoetherian W]
      (j : X ⟶ W) [IsOpenImmersion j]
      (E : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) (n : ℤ),
      DerivedCategory.IsGE E.obj n →
      DerivedCategory.IsGE
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus.obj
          E).obj n) ∧
    (∀ {W V : Scheme.{u}} [IsNoetherian W] [IsNoetherian V]
      (r : W ⟶ V) [IsProper r],
      QuasiCompact r ∧ QuasiSeparated r ∧ IsIso (fixedComparisonDirectImageMatePlus R r)) ∧
    (∀ {X W V : Scheme.{u}} [IsNoetherian X] [IsNoetherian W] [IsNoetherian V]
      (j : X ⟶ W) [IsOpenImmersion j] (r : W ⟶ V) [IsProper r],
      IsIso (finiteSiteWordComparison R j r)) ∧
    (∀ {A B C : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] [IsNoetherian C]
      (a : A ⟶ B) (b : B ⟶ C) [IsProper a] [IsProper b],
      etaleComparisonDirectImageCompIso R a b =
        conjugateIsoEquiv
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) b).comp
            (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) a))
          (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) (a ≫ b))
          (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} R) a b) ∧
      proEtaleComparisonDirectImageCompIso R a b =
        conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) b).comp
            (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) a))
          (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} R) (a ≫ b))
          (Functor.mapDerivedCategoryPlusNatIso
              (upperStarComp (ModuleCat.{u + 1} R) a b) ≪≫
            Functor.mapDerivedCategoryPlusCompIso _ _)) ∧
    (∀ {A B C : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] [IsNoetherian C]
      (a : A ⟶ B) (b : B ⟶ C) [IsProper a] [IsProper b]
      (E : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (comparisonUpperStar (ModuleCat.{u + 1} R) C).mapDerivedCategoryPlus.map
          ((etaleComparisonDirectImageCompIso R a b).hom.app E) ≫
          (fixedComparisonDirectImageMatePlus R (a ≫ b)).app E =
        (fixedComparisonDirectImageMatePlus R b).app
            ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) a).obj E) ≫
          (lowerStar (ModuleCat.{u + 1} R) b).rightDerivedFunctorPlus.map
            ((fixedComparisonDirectImageMatePlus R a).app E) ≫
          (proEtaleComparisonDirectImageCompIso R a b).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} R) A).mapDerivedCategoryPlus.obj E)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X]
      (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (fixedComparisonDirectImageMatePlus R (𝟙 X)).app E ≫
          (Functor.rightDerivedFunctorPlusNatIso
            (lowerStarId (ModuleCat.{u + 1} R) X) ≪≫
            Functor.rightDerivedFunctorPlusIdIso _).hom.app
              ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E) =
        (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.map
          ((Functor.rightDerivedFunctorPlusNatIso
            (Etale.lowerStarId (ModuleCat.{u + 1} R) X) ≪≫
            Functor.rightDerivedFunctorPlusIdIso _).hom.app E)) ∧
    (∀ {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
      (a : X ⟶ Y) (b : Y ⟶ Z) [IsOpenImmersion a] [IsOpenImmersion b]
      (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategoryPlus.map
          ((finiteSiteEtaleOpenComp R a b).hom.app E) ≫
          (properOpenSiteExtensionIso R (a ≫ b)).hom.app E =
        (properOpenSiteExtensionIso R b).hom.app
            ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) a).mapDerivedCategoryPlus.obj
              E) ≫
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) b).mapDerivedCategoryPlus.map
            ((properOpenSiteExtensionIso R a).hom.app E) ≫
          (finiteSiteProEtaleOpenComp R a b).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X]
      (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (properOpenSiteExtensionIso R (𝟙 X)).hom.app E ≫
          (finiteSiteProEtaleOpenId R X).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E) =
        (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.map
          ((finiteSiteEtaleOpenId R X).hom.app E)) ∧
    (∀ {X W₁ W₂ V : Scheme.{u}} [IsNoetherian X] [IsNoetherian W₁]
      [IsNoetherian W₂] [IsNoetherian V]
      (j₁ : X ⟶ W₁) (j₂ : X ⟶ W₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (a : W₁ ⟶ W₂) [IsProper a] (r₂ : W₂ ⟶ V) [IsProper r₂] (h : j₁ ≫ a = j₂)
      (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (comparisonUpperStar (ModuleCat.{u + 1} R) V).mapDerivedCategoryPlus.map
          (finiteSiteEtaleRefinement R j₁ j₂ a r₂ h E) ≫
          (finiteSiteWordComparison R j₁ (a ≫ r₂)).app E =
        (finiteSiteWordComparison R j₂ r₂).app E ≫
          finiteSiteProEtaleRefinement R j₁ j₂ a r₂ h E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X W _ _ j _ E n hE
    have := hE
    constructor
    · exact Functor.isGE_mapDerivedCategory_obj
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j) E.obj n
    · exact Functor.isGE_mapDerivedCategory_obj
        (comparisonUpperStar (ModuleCat.{u + 1} R) X) E.obj n
  · intro X W _ _ j _ E n hE
    have := hE
    exact (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).isGE_mapDerivedCategory_obj E.obj n
  · intro W V _ _ r _
    exact ⟨inferInstance, inferInstance, isIso_fixedComparisonDirectImageMatePlus R r⟩
  · intro X W V _ _ _ j _ r _
    have := isIso_fixedComparisonDirectImageMatePlus R r
    unfold finiteSiteWordComparison
    infer_instance
  · intro A B C _ _ _ a b _ _
    constructor
    · apply Iso.ext
      symm
      apply conjugateEquiv_eq_of_unit
      intro K
      dsimp only [Etale.derivedUpperStarLowerStarAdjunctionPlus]
      simp only [Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
      simpa only [Adjunction.comp_unit_app, etaleComparisonDirectImageCompIso,
        Category.assoc, Functor.comp_obj] using
        (Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus (ModuleCat.{u + 1} R)
          a b (a ≫ b) rfl K).symm
    · apply Iso.ext
      symm
      dsimp only [derivedUpperStarLowerStarAdjunctionPlus]
      simp only [Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
      apply conjugateEquiv_eq_of_unit
      intro K
      let M := ModuleCat.{u + 1} R
      have : (lowerStar M a).PreservesInjectiveObjects :=
        Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
          (upperStarLowerStarAdjunction M a)
      have hu (F : Sheaf (Scheme.ProEt.topology C) M) :
          (upperStarLowerStarAdjunction M (a ≫ b)).unit.app F ≫
              (lowerStar M (a ≫ b)).map ((upperStarComp M a b).hom.app F) =
            ((upperStarLowerStarAdjunction M b).comp
              (upperStarLowerStarAdjunction M a)).unit.app F ≫
              (lowerStarComp M a b).hom.app
                ((upperStar M a).obj ((upperStar M b).obj F)) := by
        have h := unit_conjugateEquiv ((upperStarLowerStarAdjunction M b).comp
          (upperStarLowerStarAdjunction M a)) (upperStarLowerStarAdjunction M (a ≫ b))
          (upperStarComp M a b).hom F
        rw [conjugateEquiv_upperStarComp_hom] at h
        exact h.symm
      have hC := Adjunction.derivedPlus_unit_comp_app
        (upperStarLowerStarAdjunction M (a ≫ b))
        ((upperStarLowerStarAdjunction M b).comp (upperStarLowerStarAdjunction M a))
        (upperStarComp M a b) (lowerStarComp M a b) hu K
      have hcomp := Adjunction.derivedPlus_comp_unit_app
        (upperStarLowerStarAdjunction M b) (upperStarLowerStarAdjunction M a) K
      have hn := (Functor.rightDerivedFunctorPlusNatTrans
        (lowerStarComp M a b).hom).naturality
          ((Functor.mapDerivedCategoryPlusCompIso
            (upperStar M b) (upperStar M a)).hom.app K)
      have hc := (Functor.rightDerivedFunctorPlusCompIso (lowerStar M a)
        (lowerStar M b)).inv.naturality ((Functor.mapDerivedCategoryPlusCompIso
          (upperStar M b) (upperStar M a)).hom.app K)
      simp only [Functor.comp_obj, Functor.comp_map] at hn hc
      symm
      change (upperStarLowerStarAdjunction M (a ≫ b)).derivedPlus.unit.app K ≫
          (lowerStar M (a ≫ b)).rightDerivedFunctorPlus.map
            ((Functor.mapDerivedCategoryPlusNatIso (upperStarComp M a b)).hom.app K ≫
              (Functor.mapDerivedCategoryPlusCompIso
                (upperStar M b) (upperStar M a)).hom.app K) = _
      rw [Functor.map_comp, ← Category.assoc, hC, Category.assoc, ← hn]
      simp only [Adjunction.comp_unit_app, Category.assoc]
      rw [← reassoc_of% hcomp]
      simp only [proEtaleComparisonDirectImageCompIso,
        Functor.rightDerivedFunctorPlusCompIso', Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app]
      erw [reassoc_of% hc, Iso.hom_inv_id_app_assoc]
      rfl
  · intro A B C _ _ _ a b _ _ E
    exact comparisonDirectImagePlus_comp R a b E
  · intro X _ E
    exact comparisonDirectImagePlus_id R X E
  · intro X Y Z _ _ _ a b _ _ E
    let M := ModuleCat.{u + 1} R
    let e (U T : Scheme.{u}) (j : U ⟶ T) [IsOpenImmersion j] :=
      openImmersionLowerShriekComparisonUpperStarIso.{u + 2, u}
        (ModuleCat.{u + 1} R) j
    have hq (F : Sheaf X.smallEtaleTopology M) :
        (e X Z (a ≫ b)).inv.app F ≫
          (comparisonUpperStar M Z).map ((Etale.openImmersionLowerShriekComp M a b).hom.app F) =
        (proEtaleOpenExtensionComp R a b).hom.app ((comparisonUpperStar M X).obj F) ≫
          (openImmersionLowerShriek M b).map ((e X Y a).inv.app F) ≫
          (e Y Z b).inv.app ((Etale.openImmersionLowerShriek M a).obj F) := by
      apply (Iso.cancel_iso_hom_right _ _
        ((e Y Z b).app ((Etale.openImmersionLowerShriek M a).obj F) ≪≫
          (openImmersionLowerShriek M b).mapIso ((e X Y a).app F) ≪≫
          (proEtaleOpenExtensionComp R a b).symm.app ((comparisonUpperStar M X).obj F))).mp
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
      simp only [Category.assoc]
      erw [(openImmersionLowerShriekComparison_coherence R).2.1 a b F]
      simp only [e, M, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp_assoc]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
      rfl
    have hd := Functor.mapDerivedCategoryPlusSquareIso_comp
      (Etale.openImmersionLowerShriek M a) (Etale.openImmersionLowerShriek M b)
      (Etale.openImmersionLowerShriek M (a ≫ b))
      (openImmersionLowerShriek M a) (openImmersionLowerShriek M b)
      (openImmersionLowerShriek M (a ≫ b))
      (comparisonUpperStar M X) (comparisonUpperStar M Y) (comparisonUpperStar M Z)
      (e X Y a).symm (e Y Z b).symm (e X Z (a ≫ b)).symm
      (Etale.openImmersionLowerShriekComp M a b) (proEtaleOpenExtensionComp R a b) hq E
    dsimp only [e, M] at hd
    rw [siteExtension_symm, siteExtension_symm, siteExtension_symm] at hd
    have he := congrArg Iso.inv (etaleOpenComp_symm R a b)
    have hp := congrArg Iso.inv (proEtaleOpenComp_symm R a b)
    simp only [Iso.symm_inv] at he hp
    rw [← he, ← hp] at hd
    simp only [Iso.symm_hom] at hd
    change (properOpenSiteExtensionIso R (a ≫ b)).inv.app E ≫
        (comparisonUpperStar M Z).mapDerivedCategoryPlus.map
          ((finiteSiteEtaleOpenComp R a b).inv.app E) =
      (finiteSiteProEtaleOpenComp R a b).inv.app
          ((comparisonUpperStar M X).mapDerivedCategoryPlus.obj E) ≫
        (openImmersionLowerShriek M b).mapDerivedCategoryPlus.map
          ((properOpenSiteExtensionIso R a).inv.app E) ≫
        (properOpenSiteExtensionIso R b).inv.app
          ((Etale.openImmersionLowerShriek M a).mapDerivedCategoryPlus.obj E) at hd
    have hi := congrArg Iso.inv (show
      (properOpenSiteExtensionIso R (a ≫ b)).symm.app E ≪≫
          (comparisonUpperStar M Z).mapDerivedCategoryPlus.mapIso
            ((finiteSiteEtaleOpenComp R a b).symm.app E) =
        (finiteSiteProEtaleOpenComp R a b).symm.app
            ((comparisonUpperStar M X).mapDerivedCategoryPlus.obj E) ≪≫
          (openImmersionLowerShriek M b).mapDerivedCategoryPlus.mapIso
            ((properOpenSiteExtensionIso R a).symm.app E) ≪≫
          (properOpenSiteExtensionIso R b).symm.app
            ((Etale.openImmersionLowerShriek M a).mapDerivedCategoryPlus.obj E)
      from Iso.ext hd)
    simpa only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
      Category.assoc] using hi
  · intro X _ E
    let M := ModuleCat.{u + 1} R
    let eE := Adjunction.leftAdjointIdIso
      (Etale.openImmersionLowerShriekUpperStarAdjunction M (𝟙 X)) (Etale.upperStarId M X)
    let eP := Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction M (𝟙 X)) (upperStarId M X)
    have hq (F : Sheaf X.smallEtaleTopology M) :
        (openImmersionLowerShriekComparisonUpperStarIso.{u + 2, u} M (𝟙 X)).inv.app F ≫
          (comparisonUpperStar M X).map (eE.hom.app F) =
        eP.hom.app ((comparisonUpperStar M X).obj F) := by
      apply (cancel_epi
        ((openImmersionLowerShriekComparisonUpperStarIso.{u + 2, u} M (𝟙 X)).hom.app F)).mp
      simp only [Iso.hom_inv_id_app_assoc]
      exact ((openImmersionLowerShriekComparison_coherence R).2.2 X F).symm
    have hd := square_identity (comparisonUpperStar M X)
      (openImmersionLowerShriek M (𝟙 X)) (Etale.openImmersionLowerShriek M (𝟙 X))
      (openImmersionLowerShriekComparisonUpperStarIso.{u + 2, u} M (𝟙 X)).symm eE eP hq E
    dsimp only [M] at hd
    rw [siteExtension_symm] at hd
    simp only [Iso.symm_hom] at hd
    change (properOpenSiteExtensionIso R (𝟙 X)).inv.app E ≫
      (comparisonUpperStar M X).mapDerivedCategoryPlus.map
        ((finiteSiteEtaleOpenId R X).hom.app E) =
      (finiteSiteProEtaleOpenId R X).hom.app
        ((comparisonUpperStar M X).mapDerivedCategoryPlus.obj E) at hd
    apply (cancel_epi ((properOpenSiteExtensionIso R (𝟙 X)).inv.app E)).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hd.symm
  · intro X W₁ W₂ V _ _ _ _ j₁ j₂ _ _ a _ r₂ _ h E
    simp only [finiteSiteEtaleRefinement, finiteSiteProEtaleRefinement,
      finiteSiteWordComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.map_comp, Category.assoc]
    erw [reassoc_of% (comparisonDirectImagePlus_comp R a r₂ _)]
    have hp := (proEtaleComparisonDirectImageCompIso R a r₂).hom.naturality
      ((properOpenSiteExtensionIso R j₁).hom.app E)
    dsimp only [Functor.comp_map] at hp
    erw [← hp]
    have hn := (fixedComparisonDirectImageMatePlus R r₂).naturality
      (Etale.properOpenComparison R a j₁ j₂ h E)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    have ho : (properOpenSiteExtensionIso R j₂).hom.app E ≫
        (properOpenProEtaleIsoPlus R a j₁ j₂ h E).hom =
      (comparisonUpperStar (ModuleCat.{u + 1} R) W₂).mapDerivedCategoryPlus.map
          (Etale.properOpenComparison R a j₁ j₂ h E) ≫
        (fixedComparisonDirectImageMatePlus R a).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j₁).mapDerivedCategoryPlus.obj
            E) ≫
        (lowerStar (ModuleCat.{u + 1} R) a).rightDerivedFunctorPlus.map
          ((properOpenSiteExtensionIso R j₁).hom.app E) := by
      simp only [properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, Functor.mapIso_hom, asIso_hom, fixedComparisonDirectImageMatePlus,
        Iso.hom_inv_id_app_assoc]
    simpa only [Functor.map_comp, Category.assoc, fixedComparisonDirectImageMatePlus,
      Functor.comp_obj, Etale.rightDerivedLowerStarPlus] using
      congrArg (fun t ↦ (fixedComparisonDirectImageMatePlus R r₂).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j₂).mapDerivedCategoryPlus.obj
          E) ≫
        (lowerStar (ModuleCat.{u + 1} R) r₂).rightDerivedFunctorPlus.map t ≫
        (proEtaleComparisonDirectImageCompIso R a r₂).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j₁).mapDerivedCategoryPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)))
        ho.symm

end AlgebraicGeometry.ProEtale
