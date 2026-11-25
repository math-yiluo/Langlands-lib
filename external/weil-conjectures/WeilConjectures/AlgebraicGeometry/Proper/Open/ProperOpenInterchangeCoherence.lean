/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangePasting
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeGeometricNormalization

/-!
# Proper/open interchange and its coherence

## References

* Stacks Project, More on Étale Cohomology, Tags 0F7B, 0F7C, 0F7D, 0F7F

## Implementation details

In `properOpenInterchangeCoherence`, the ordinary isomorphism `δ` is fixed by equality in the
common ordinary direct image. The unit equation is the resolution-independent form of the
K-injective normalization: on an injective representative the left unit is invertible; the
right unit is represented by applying `p_*` to a K-injective replacement of `k_!J`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Use the additive structure carried by the abelian instance in the derived APIs.
-- This avoids repeatedly comparing it with the full-subcategory additive structure.
attribute [local instance 2000] Abelian.toPreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Upstream's `Mono (f.app k)` instance searches for pullbacks of étale sheaves through
-- `ModuleCat.instHasLimitsOfSize`, which leaves universe constraints stuck.
attribute [-instance] CategoryTheory.instMonoAppOfFunctor

private theorem derived_base_change_unit
    {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    (G : B ⥤ C) (G' : B' ⥤ C') (β : B ⥤ B') (γ : C ⥤ C')
    [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
    (e : G ⋙ γ ⟶ β ⋙ G') (J : HomotopyCategory.Plus B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnith.app J) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Qh.obj J) =
      γ.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj J) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app J) ≫
        G'.rightDerivedFunctorPlusUnith.app (β.mapHomotopyCategoryPlus.obj J) ≫
        G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app J) := by
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e) J
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Category.comp_id,
    Category.id_comp, Category.assoc, CategoryTheory.Functor.map_id] at hf
  simp only [Functor.comp_obj] at hf
  erw [Category.id_comp, Category.id_comp] at hf
  exact hf

private theorem normalized_base_change_unit
    {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    (G : B ⥤ C) (G' : B' ⥤ C') (β : B ⥤ B') (γ : C ⥤ C')
    [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
    (e : G ⋙ γ ⟶ β ⋙ G')
    (c : G.rightDerivedFunctorPlus ⋙ γ.mapDerivedCategoryPlus ⟶
      β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus)
    (hc : c = Functor.rightDerivedFunctorPlusBaseChange e)
    (J : HomotopyCategory.Plus B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnith.app J) ≫
        c.app (DerivedCategory.Plus.Qh.obj J) =
      γ.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj J) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app J) ≫
        G'.rightDerivedFunctorPlusUnith.app (β.mapHomotopyCategoryPlus.obj J) ≫
        G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app J) := by
  rw [hc]
  exact derived_base_change_unit G G' β γ e J

private theorem exact_identity_fac
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (E : A ⥤ A) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (e : E ≅ 𝟭 A) (J : HomotopyCategory.Plus A) :
    (Functor.mapDerivedCategoryPlusNatIso e ≪≫
        Functor.mapDerivedCategoryPlusIdIso A).hom.app (DerivedCategory.Plus.Qh.obj J) =
      E.mapDerivedCategoryPlusFactorsh.hom.app J ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app J) := by
  rw [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

private theorem derived_horizontal_identity
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (G : A ⥤ B) (E : A ⥤ A) (F : B ⥤ B)
    [G.Additive] [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (eE : E ≅ 𝟭 A) (eF : F ≅ 𝟭 B) (δ : G ⋙ F ≅ E ⋙ G)
    (γ : G.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus ≅
      E.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus)
    (hδ : ∀ X, δ.hom.app X ≫ G.map (eE.hom.app X) = eF.hom.app (G.obj X))
    (hγ : γ.hom = Functor.rightDerivedFunctorPlusBaseChange δ.hom)
    (K : DerivedCategory.Plus A) :
    γ.hom.app K ≫ G.rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusNatIso eE ≪≫
          Functor.mapDerivedCategoryPlusIdIso A).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso eF ≪≫
        Functor.mapDerivedCategoryPlusIdIso B).hom.app (G.rightDerivedFunctorPlus.obj K) := by
  let eED := Functor.mapDerivedCategoryPlusNatIso eE ≪≫
    Functor.mapDerivedCategoryPlusIdIso A
  let eFD := Functor.mapDerivedCategoryPlusNatIso eF ≪≫
    Functor.mapDerivedCategoryPlusIdIso B
  let a : G.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus ⟶
      G.rightDerivedFunctorPlus :=
    γ.hom ≫ Functor.whiskerRight eED.hom G.rightDerivedFunctorPlus
  let b : G.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus ⟶
      G.rightDerivedFunctorPlus := Functor.whiskerLeft G.rightDerivedFunctorPlus eFD.hom
  have hab : a = b := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus)
      (Functor.whiskerRight G.rightDerivedFunctorPlusUnith F.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso A)
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.assoc]
    simp only [Functor.comp_obj]
    erw [Category.id_comp, Category.id_comp]
    erw [hγ, reassoc_of% derived_base_change_unit G G E F δ.hom J]
    erw [← G.rightDerivedFunctorPlus.map_comp, exact_identity_fac E eE J,
      Iso.inv_hom_id_app_assoc]
    have hn := G.rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus eE.hom).app J)
    simp only [Functor.comp_map] at hn
    erw [← hn]
    have hf := eFD.hom.naturality (G.rightDerivedFunctorPlusUnith.app J)
    simp only [Functor.id_map] at hf
    erw [hf, exact_identity_fac F eF (G.mapHomotopyCategoryPlus.obj J)]
    have ht : δ.hom ≫ Functor.whiskerRight eE.hom G =
        Functor.whiskerLeft G eF.hom := by
      ext X
      exact hδ X
    have hh := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus ht) J
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at hh
    change (NatTrans.mapHomotopyCategoryPlus δ.hom).app J ≫
        G.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus eE.hom).app J) =
      (NatTrans.mapHomotopyCategoryPlus eF.hom).app (G.mapHomotopyCategoryPlus.obj J) at hh
    erw [← DerivedCategory.Plus.Qh.map_comp_assoc, hh]
    erw [Category.assoc]
    rfl
  exact congr_app hab K

private theorem open_identity_comparison
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).app F ≫
        (lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app F := by
  let adj := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)
  let e := upperStarId (ModuleCat.{u + 1} Λ) X
  let l := Adjunction.leftAdjointIdIso adj e
  apply (adj.homEquiv F F).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hl := unit_conjugateEquiv Adjunction.id adj l.hom F
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at hl
  have hl' : e.inv.app F = adj.unit.app F ≫
      (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)).map (l.hom.app F) := by
    change 𝟙 F ≫ e.inv.app F = _ at hl
    simpa only [Category.id_comp] using hl
  erw [← hl']
  have hh : (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)).map
        ((lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit.app F ≫
        e.inv.app F := by
    apply (cancel_mono (e.hom.app F)).1
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    have hn := e.hom.naturality ((lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F)
    simp only [Functor.id_map] at hn
    erw [hn, ← upperStarId_inv_app_counit_app, Iso.hom_inv_id_app_assoc]
  rw [CategoryTheory.Functor.map_comp]
  erw [hh]
  have hn := unit_map_openImmersionLowerShriekToLowerStar_app_counit
    (ModuleCat.{u + 1} Λ) (𝟙 X) F
  have hn' := congrArg (fun z ↦ z ≫ e.inv.app F) hn
  erw [Category.id_comp] at hn'
  simpa only [Category.assoc] using hn'

private theorem ordinary_identity_horizontal
    (Λ : Type (u + 1)) [CommRing Λ]
    {A C : Scheme.{u}} (r : A ⟶ C)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 C) ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 A) ⋙
        lowerStar (ModuleCat.{u + 1} Λ) r)
    (hn : ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) r).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 C)).app
        ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r (𝟙 C) ((𝟙 A) ≫ r)
          ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app F)
    (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
        ((Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A))
          (upperStarId (ModuleCat.{u + 1} Λ) A)).hom.app F) =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C))
        (upperStarId (ModuleCat.{u + 1} Λ) C)).hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) := by
  have hnaux (f : A ⟶ C) (hf : f = (𝟙 A) ≫ r) :
      δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) r f hf).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 C)).app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) r (𝟙 C) f
            (hf.trans ((Category.id_comp r).trans (Category.comp_id r).symm))).hom.app F := by
    subst f
    exact hn F
  have hn' := hnaux r (Category.id_comp r).symm
  rw [lowerStarComp_id_left, lowerStarComp_id_right] at hn'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app] at hn'
  erw [Category.comp_id, Category.comp_id] at hn'
  rw [← open_identity_comparison Λ A F,
    ← open_identity_comparison Λ C ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F),
    CategoryTheory.Functor.map_comp, ← Category.assoc]
  exact hn'

private theorem derived_vertical_identity
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
    (G : A ⥤ A) (H : B ⥤ B) (E : A ⥤ B)
    [G.Additive] [H.Additive] [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (eG : G ≅ 𝟭 A) (eH : H ≅ 𝟭 B) (δ : G ⋙ E ⟶ E ⋙ H)
    (γ : G.rightDerivedFunctorPlus ⋙ E.mapDerivedCategoryPlus ⟶
      E.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus)
    (hδ : ∀ F, δ.app F ≫ eH.hom.app (E.obj F) = E.map (eG.hom.app F))
    (hγ : γ = Functor.rightDerivedFunctorPlusBaseChange δ)
    (ia : G.rightDerivedFunctorPlus ⟶ 𝟭 (DerivedCategory.Plus A))
    (ib : H.rightDerivedFunctorPlus ⟶ 𝟭 (DerivedCategory.Plus B))
    (ha : ∀ J, G.rightDerivedFunctorPlusUnith.app J ≫
      ia.app (DerivedCategory.Plus.Qh.obj J) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus eG.hom).app J))
    (hb : ∀ J, H.rightDerivedFunctorPlusUnith.app J ≫
      ib.app (DerivedCategory.Plus.Qh.obj J) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus eH.hom).app J))
    (K : DerivedCategory.Plus A) :
    γ.app K ≫ ib.app (E.mapDerivedCategoryPlus.obj K) =
      E.mapDerivedCategoryPlus.map (ia.app K) := by
  let a : G.rightDerivedFunctorPlus ⋙ E.mapDerivedCategoryPlus ⟶
      E.mapDerivedCategoryPlus := γ ≫ Functor.whiskerLeft E.mapDerivedCategoryPlus ib
  let b : G.rightDerivedFunctorPlus ⋙ E.mapDerivedCategoryPlus ⟶
      E.mapDerivedCategoryPlus := Functor.whiskerRight ia E.mapDerivedCategoryPlus
  have hab : a = b := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctorPlus ⋙ E.mapDerivedCategoryPlus)
      (Functor.whiskerRight G.rightDerivedFunctorPlusUnith E.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso A)
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.assoc]
    simp only [Functor.comp_obj]
    erw [Category.id_comp, Category.id_comp]
    erw [hγ, reassoc_of% derived_base_change_unit G H E E δ J]
    have hn := ib.naturality (E.mapDerivedCategoryPlusFactorsh.inv.app J)
    simp only [Functor.id_map] at hn
    erw [hn]
    erw [reassoc_of% hb (E.mapHomotopyCategoryPlus.obj J)]
    have ht : δ ≫ Functor.whiskerLeft E eH.hom =
        Functor.whiskerRight eG.hom E := by
      ext F
      exact hδ F
    have hh := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus ht) J
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at hh
    change (NatTrans.mapHomotopyCategoryPlus δ).app J ≫
        (NatTrans.mapHomotopyCategoryPlus eH.hom).app (E.mapHomotopyCategoryPlus.obj J) =
      E.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus eG.hom).app J) at hh
    erw [← DerivedCategory.Plus.Qh.map_comp_assoc, hh]
    have he := E.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus eG.hom).app J)
    simp only [Functor.comp_map] at he
    erw [← reassoc_of% he]
    erw [E.mapDerivedCategoryPlusFactorsh.hom_inv_id_app J, Category.comp_id]
    erw [← E.mapDerivedCategoryPlus.map_comp, ha]
  exact congr_app hab K

private theorem ordinary_interchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
    (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ∃ δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p,
      ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F := by
  classical
  obtain ⟨L, ι, _, hp, ho, c, _, hc, _, _⟩ := properSupportSheafComposition Λ
  have hproper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsIso (ι f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hp X Y f
  have hc' (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
      [IsSeparated fg] [LocallyOfFiniteType fg] (hfg : fg = f ≫ g) :
      ∃ cc : L f ⋙ L g ≅ L fg, ∀ F,
        cc.hom.app F ≫ (ι fg).app F =
          (ι g).app ((L f).obj F) ≫ (lowerStar (ModuleCat.{u + 1} Λ) g).map
            ((ι f).app F) ≫ (lowerStarComp (ModuleCat.{u + 1} Λ) f g fg hfg).hom.app F := by
    subst fg
    exact ⟨c X Y Z f g, hc X Y Z f g⟩
  have := hproper r
  have := hproper p
  obtain ⟨oi, hoi⟩ := ho C D i
  obtain ⟨ok, hok⟩ := ho A B k
  obtain ⟨cri, hcri⟩ := hc' A C D r i (k ≫ p) h
  let ar := Functor.isoWhiskerRight (asIso (ι r)).symm
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≪≫
    Functor.isoWhiskerLeft (L r) oi ≪≫ cri
  let bk := Functor.isoWhiskerRight ok (lowerStar (ModuleCat.{u + 1} Λ) p) ≪≫
    Functor.isoWhiskerLeft (L k) (asIso (ι p)).symm ≪≫ c A B D k p
  refine ⟨ar ≪≫ bk.symm, fun F ↦ ?_⟩
  have ha : ar.hom.app F ≫ (ι (k ≫ p)).app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
        ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F := by
    dsimp only [ar, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom]
    rw [Category.assoc, Category.assoc, hcri]
    have hoi' := congr_app hoi ((L r).obj F)
    dsimp only [NatTrans.comp_app] at hoi'
    rw [reassoc_of% hoi', reassoc_of%
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).naturality
        ((asIso (ι r)).inv.app F))]
    have hh : (asIso (ι r)).inv.app F ≫ (ι r).app F = 𝟙 _ :=
      (asIso (ι r)).inv_hom_id_app F
    rw [← Functor.map_comp_assoc, hh, CategoryTheory.Functor.map_id, Category.id_comp]
  have hb : bk.hom.app F ≫ (ι (k ≫ p)).app F =
      (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F := by
    dsimp only [bk, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom]
    rw [Category.assoc, Category.assoc, hc]
    have hh : (asIso (ι p)).inv.app ((L k).obj F) ≫
        (ι p).app ((L k).obj F) = 𝟙 _ := (asIso (ι p)).inv_hom_id_app _
    rw [reassoc_of% hh, ← Functor.map_comp_assoc]
    have hok' := congr_app hok F
    dsimp only [NatTrans.comp_app] at hok'
    rw [hok']
  rw [← hb]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact ha

private theorem rightAcyclic_of_plus_vanishing
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (G : A ⥤ B) [G.Additive] (X : A)
    (h : ∀ n : ℕ, IsZero ((DerivedCategory.Plus.homologyFunctor B (n + 1)).obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) :
    G.rightAcyclic X := by
  intro q
  exact (h q).of_iso (G.homologyRightDerivedFunctorPlusObjSingleFunctorIso X (q + 1)).symm

private theorem interchange_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
    (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ∀ (J : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J],
      (lowerStar (ModuleCat.{u + 1} Λ) p).rightAcyclic
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj J) := by
    intro J _
    apply rightAcyclic_of_plus_vanishing
    intro q
    exact isZero_higherDirectImage_openImmersionLowerShriek_injective Λ k i r p h J
      (q + 1) (by omega)

private noncomputable def ordinaryInterchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
    (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
     lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  (ordinary_interchange Λ k i r p h).choose

private noncomputable def derivedInterchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
    (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p) :
     (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus := by
  have := Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic δ
    (interchange_acyclic Λ k i r p h)
  exact asIso (Functor.rightDerivedFunctorPlusBaseChange δ.hom)

private noncomputable def derivedInterchangeFamily
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
        ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ ((lowerStar (ModuleCat.{u + 1} Λ)
          p).rightDerivedFunctorPlus) :=
          fun {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) ↦
    derivedInterchange Λ k i r p h (ordinaryInterchange Λ k i r p h)

private theorem open_compare_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (k : X ⟶ Y) [IsOpenImmersion k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) := by
  obtain ⟨L, ι, hi, _, ho, _⟩ := properSupportSheafComposition Λ
  have hι : Mono ((ι k).app F) := by
    refine ⟨fun {Z} a b hab ↦ ?_⟩
    ext V s
    apply (hi X Y k F V.unop).1
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun z ↦ z.hom) hab) V) s
  obtain ⟨o, he⟩ := ho X Y k
  have he' := congr_app he F
  dsimp only [NatTrans.comp_app] at he'
  rw [← he']
  infer_instance

private theorem ordinary_identity_vertical
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}}
    (k : A ⟶ B) [IsOpenImmersion k]
    (δ : lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
    (hn : ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B)).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k (k ≫ 𝟙 B)
            ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app F)
    (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    δ.hom.app F ≫ (lowerStarId (ModuleCat.{u + 1} Λ) B).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj F) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
        ((lowerStarId (ModuleCat.{u + 1} Λ) A).hom.app F) := by
  have := open_compare_mono Λ k F
  apply (cancel_mono
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F)).1
  have hnaux (f : A ⟶ B) (hf : f = k ≫ 𝟙 B) :
      δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B) f hf).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k f
            (hf.trans ((Category.comp_id k).trans (Category.id_comp k).symm))).hom.app F := by
    subst f
    exact hn F
  have hn' : δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B) k
            (Category.comp_id k).symm).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k k
            (Category.id_comp k).symm).hom.app F := by
    exact hnaux k (Category.comp_id k).symm
  rw [lowerStarComp_id_right, lowerStarComp_id_left] at hn'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hn'
  erw [Category.comp_id, Category.comp_id] at hn'
  simp only [Category.assoc]
  have hid := (lowerStarId (ModuleCat.{u + 1} Λ) B).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F)
  simp only [Functor.id_map] at hid
  rw [← hid, hn']
  exact ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).naturality
    ((lowerStarId (ModuleCat.{u + 1} Λ) A).hom.app F)).symm

private theorem generic_vertical_pasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂]
    [Category* B₀] [Category* B₁] [Category* B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
    [EnoughInjectives A₀] [EnoughInjectives A₁]
    [EnoughInjectives B₀] [EnoughInjectives B₁]
    (G₁ : A₀ ⥤ A₁) (G₂ : A₁ ⥤ A₂) (G : A₀ ⥤ A₂)
    (H₁ : B₀ ⥤ B₁) (H₂ : B₁ ⥤ B₂) (H : B₀ ⥤ B₂)
    (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (E₂ : A₂ ⥤ B₂)
    [G₁.Additive] [G₂.Additive] [G.Additive]
    [H₁.Additive] [H₂.Additive] [H.Additive]
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
    [G₁.PreservesInjectiveObjects] [H₁.PreservesInjectiveObjects]
    (g : G₁ ⋙ G₂ ≅ G) (h : H₁ ⋙ H₂ ≅ H)
    (e₁ : G₁ ⋙ E₁ ⟶ E₀ ⋙ H₁) (e₂ : G₂ ⋙ E₂ ⟶ E₁ ⋙ H₂)
    (e : G ⋙ E₂ ⟶ E₀ ⋙ H)
    (he : ∀ X, E₂.map (g.hom.app X) ≫ e.app X =
      e₂.app (G₁.obj X) ≫ H₂.map (e₁.app X) ≫ h.hom.app (E₀.obj X))
    (c₁ : G₁.rightDerivedFunctorPlus ⋙ E₁.mapDerivedCategoryPlus ⟶
      E₀.mapDerivedCategoryPlus ⋙ H₁.rightDerivedFunctorPlus)
    (c₂ : G₂.rightDerivedFunctorPlus ⋙ E₂.mapDerivedCategoryPlus ⟶
      E₁.mapDerivedCategoryPlus ⋙ H₂.rightDerivedFunctorPlus)
    (c : G.rightDerivedFunctorPlus ⋙ E₂.mapDerivedCategoryPlus ⟶
      E₀.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus)
    (hc₁ : c₁ = Functor.rightDerivedFunctorPlusBaseChange e₁)
    (hc₂ : c₂ = Functor.rightDerivedFunctorPlusBaseChange e₂)
    (hc : c = Functor.rightDerivedFunctorPlusBaseChange e)
    (K : DerivedCategory.Plus A₀) :
    E₂.mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' G₁ G₂ g).hom.app K) ≫
        c.app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' H₁ H₂ h).inv.app
          (E₀.mapDerivedCategoryPlus.obj K) =
      c₂.app (G₁.rightDerivedFunctorPlus.obj K) ≫
        H₂.rightDerivedFunctorPlus.map
          (c₁.app K) := by
  rw [hc₁, hc₂, hc]
  let cG := Functor.rightDerivedFunctorPlusCompIso' G₁ G₂ g
  let cH := Functor.rightDerivedFunctorPlusCompIso' H₁ H₂ h
  let a : (G₁.rightDerivedFunctorPlus ⋙ G₂.rightDerivedFunctorPlus) ⋙
      E₂.mapDerivedCategoryPlus ⟶ E₀.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus :=
    Functor.whiskerRight cG.hom E₂.mapDerivedCategoryPlus ≫
      Functor.rightDerivedFunctorPlusBaseChange e
  let b : (G₁.rightDerivedFunctorPlus ⋙ G₂.rightDerivedFunctorPlus) ⋙
      E₂.mapDerivedCategoryPlus ⟶ E₀.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft G₁.rightDerivedFunctorPlus
        (Functor.rightDerivedFunctorPlusBaseChange e₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusBaseChange e₁)
        H₂.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E₀.mapDerivedCategoryPlus cH.hom
  have hi (X : HomotopyCategory.Plus (InjectiveObject A₀)) :
      IsIso ((Functor.rightDerivedFunctorPlusCompUnit G₁ G₂).app
        ((InjectiveObject.ι A₀).mapHomotopyCategoryPlus.obj X)) := by
    let J := (InjectiveObject.ι A₀).mapHomotopyCategoryPlus.obj X
    have hJ : ∀ n : ℤ, Injective (J.obj.as.X n) := fun n ↦ inferInstance
    have : IsIso (G₁.rightDerivedFunctorPlusUnith.app J) := inferInstance
    have hGJ : ∀ n : ℤ, Injective ((G₁.mapHomotopyCategoryPlus.obj J).obj.as.X n) :=
      fun n ↦ inferInstanceAs (Injective (G₁.obj (J.obj.as.X n)))
    have : IsIso (G₂.rightDerivedFunctorPlusUnith.app (G₁.mapHomotopyCategoryPlus.obj J)) := by
      have := hGJ
      infer_instance
    change IsIso ((Functor.rightDerivedFunctorPlusCompUnit G₁ G₂).app J)
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    infer_instance
  have : ((G₁.rightDerivedFunctorPlus ⋙ G₂.rightDerivedFunctorPlus) ⋙
      E₂.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompUnit G₁ G₂)
        E₂.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.Plus.quasiIso A₀) := by
    refine (HomotopyCategory.Plus.localizerMorphism_derives
      (((G₁ ⋙ G₂).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        E₂.mapDerivedCategoryPlus)).isRightDerivedFunctor_of_isIso _ (fun X ↦ ?_)
    have := hi X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    infer_instance
  have hab : a = b := by
    apply Functor.rightDerived_ext
      ((G₁.rightDerivedFunctorPlus ⋙ G₂.rightDerivedFunctorPlus) ⋙ E₂.mapDerivedCategoryPlus)
      (Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompUnit G₁ G₂)
        E₂.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.Plus.quasiIso A₀)
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.assoc]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.id_comp]
    have hcG := congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac G₁ G₂ g) J
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hcG
    erw [← E₂.mapDerivedCategoryPlus.map_comp_assoc, hcG,
      E₂.mapDerivedCategoryPlus.map_comp]
    simp only [Category.assoc]
    erw [derived_base_change_unit G H E₀ E₂ e J]
    have hn₂ := (Functor.rightDerivedFunctorPlusBaseChange e₂).naturality
      (G₁.rightDerivedFunctorPlusUnith.app J)
    simp only [Functor.comp_map] at hn₂
    rw [Functor.rightDerivedFunctorPlusCompUnit_app, E₂.mapDerivedCategoryPlus.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% hn₂]
    erw [reassoc_of% derived_base_change_unit G₂ H₂ E₁ E₂ e₂
      (G₁.mapHomotopyCategoryPlus.obj J)]
    have h₁ := derived_base_change_unit G₁ H₁ E₀ E₁ e₁ J
    have h₁' : E₁.mapDerivedCategoryPlusFactorsh.inv.app
        (G₁.mapHomotopyCategoryPlus.obj J) ≫
        E₁.mapDerivedCategoryPlus.map (G₁.rightDerivedFunctorPlusUnith.app J) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e₁).app
          (DerivedCategory.Plus.Qh.obj J) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e₁).app J) ≫
        H₁.rightDerivedFunctorPlusUnith.app (E₀.mapHomotopyCategoryPlus.obj J) ≫
        H₁.rightDerivedFunctorPlus.map (E₀.mapDerivedCategoryPlusFactorsh.inv.app J) := by
      apply (cancel_epi (E₁.mapDerivedCategoryPlusFactorsh.hom.app
        (G₁.mapHomotopyCategoryPlus.obj J))).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      simpa only [Category.assoc] using h₁
    erw [← H₂.rightDerivedFunctorPlus.map_comp_assoc,
      ← H₂.rightDerivedFunctorPlus.map_comp_assoc]
    simp only [Category.assoc]
    erw [h₁']
    rw [H₂.rightDerivedFunctorPlus.map_comp, H₂.rightDerivedFunctorPlus.map_comp]
    simp only [Category.assoc]
    have hn := H₂.rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus e₁).app J)
    simp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hnH := cH.hom.naturality (E₀.mapDerivedCategoryPlusFactorsh.inv.app J)
    simp only [Functor.comp_map] at hnH
    erw [hnH]
    have hcH := congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac H₁ H₂ h)
      (E₀.mapHomotopyCategoryPlus.obj J)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightDerivedFunctorPlusCompUnit_app] at hcH
    erw [reassoc_of% hcH]
    have hnE := E₂.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus g.hom).app J)
    simp only [Functor.comp_map] at hnE
    erw [reassoc_of% hnE]
    have ht : Functor.whiskerRight g.hom E₂ ≫ e =
        Functor.whiskerLeft G₁ e₂ ≫ Functor.whiskerRight e₁ H₂ ≫
          Functor.whiskerLeft E₀ h.hom := by
      ext X
      exact he X
    have hh := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus ht) J
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
      NatTrans.mapHomotopyCategoryPlus_whiskerRight_app,
      NatTrans.mapHomotopyCategoryPlus_whiskerLeft_app] at hh
    erw [← DerivedCategory.Plus.Qh.map_comp_assoc, hh]
    simp only [DerivedCategory.Plus.Qh.map_comp, Category.assoc]
    rfl
  change E₂.mapDerivedCategoryPlus.map (cG.hom.app K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange e).app K ≫
      cH.inv.app (E₀.mapDerivedCategoryPlus.obj K) = _
  apply (cancel_mono (cH.hom.app (E₀.mapDerivedCategoryPlus.obj K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  simpa only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Category.id_comp] using congr_app hab K

private theorem ordinary_vertical (Λ : Type (u + 1)) [CommRing Λ]
    (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
    (hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F))
    {A B C D E F : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
    (X : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).map ((lowerStarComp (ModuleCat.{u + 1} Λ)
      r₁ r₂).hom.app X) ≫
        (δ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom.app X =
      (δ i j r₂ p₂ h₂).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) r₁).obj X) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p₂).map ((δ k i r₁ p₁ h₁).hom.app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) k).obj X) := by
  have := open_compare_mono Λ k X
  apply (cancel_mono ((lowerStar (ModuleCat.{u + 1} Λ) (p₁ ≫ p₂)).map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) k (p₁ ≫ p₂)).hom.app X)).1
  simp only [Category.assoc]
  rw [hδ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h]
  have nc := (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X)
  simp only [Functor.comp_map] at nc
  rw [← reassoc_of% nc]
  have hk := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) k p₁ p₂ (k ≫ p₁) (p₁ ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) rfl rfl (Category.assoc k p₁ p₂).symm) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hk
  rw [← hk, ← (lowerStar (ModuleCat.{u + 1} Λ) p₂).map_comp_assoc, ← (lowerStar (ModuleCat.{u + 1}
    Λ) p₂).map_comp_assoc]
  simp only [Category.assoc]
  rw [hδ k i r₁ p₁ h₁]
  rw [(lowerStar (ModuleCat.{u + 1} Λ) p₂).map_comp]
  simp only [Category.assoc]
  have hi := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) r₁ i p₂ (k ≫ p₁) (i ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) h₁ rfl (Category.assoc k p₁ p₂).symm) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hi
  rw [hi, reassoc_of% hδ i j r₂ p₂ h₂ ((lowerStar (ModuleCat.{u + 1} Λ) r₁).obj X)]
  have nj := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).naturality
    ((lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂).hom.app X)
  rw [reassoc_of% nj]
  have hr := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) r₁ r₂ j (r₁ ≫ r₂) (i ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) rfl h₂ h) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hr
  rw [hr]

set_option linter.unusedVariables false in
/-- The family of underived proper/open isomorphisms. -/
def ProperOpenUnderivedFamily (Λ : Type (u + 1)) [CommRing Λ] :=
  ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p)

set_option linter.unusedVariables false in
/-- The family of derived proper/open isomorphisms. -/
def ProperOpenDerivedFamily (Λ : Type (u + 1)) [CommRing Λ] :=
  ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p)

set_option linter.unusedVariables false in
/-- The joint section, derived-unit, refinement, composition, identity and
base-change normalizations of a pair of finite proper/open comparison families.
Naming this predicate keeps its full conjunction out of witness-selection terms. -/
def properOpenInterchangeConditions (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (δ : ProperOpenUnderivedFamily Λ) (γ : ProperOpenDerivedFamily Λ) :
    Prop :=
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (J :
        HomotopyCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map ((lowerStar
        (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusUnith.app J) ≫
        (γ k i r p h).hom.app (DerivedCategory.Plus.Qh.obj J) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusFactorsh.hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomotopyCategoryPlus.obj J) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus (δ k i r p h).hom).app J) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusUnith.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomotopyCategoryPlus.obj J) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlusFactorsh.inv.app J)) ∧
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (γ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom.app K =
      properOpenComparison Λ p j₁ j₂ h K) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar
        (ModuleCat.{u + 1} Λ) r₂) (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)).hom.app K) ≫
        (γ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom.app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) p₁) (lowerStar
        (ModuleCat.{u + 1} Λ) p₂) (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (γ i j r₂ p₂ h₂).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r₁).obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₂).map ((γ k i r₁ p₁ h₁).hom.app K)) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1}
        Λ) r).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) q).map ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {A B : Scheme.{u}} (k : A ⟶ B) [IsOpenImmersion k]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ k k (𝟙 A) (𝟙 B) ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).hom.app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).hom.app K)) ∧
    (∀ {A C : Scheme.{u}} (r : A ⟶ C) [IsProper r]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ (𝟙 A) (𝟙 C) r r ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).map
        ((Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A)) (upperStarId
        (ModuleCat.{u + 1} Λ) A)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C)) (upperStarId
        (ModuleCat.{u + 1} Λ) C)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj K)) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map ((γ k i r p h).hom.app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₁).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u
        + 1} Λ) r).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (γ k₁ i₁ r₁ p₁ h₁).hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K))

set_option linter.unusedVariables false in
/-- The canonical proper/open interchange isomorphism, normalized by the derived units,
with refinement normalization, vertical and horizontal composition, identities and base change.
-/
theorem properOpenInterchangeCoherence (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ δ γ, properOpenInterchangeConditions Λ δ γ := by
  have hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
    [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      ((@ordinaryInterchange Λ _) k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F) := by
    intro A B C D k i r p _ _ _ _ h F
    exact (ordinary_interchange Λ k i r p h).choose_spec F
  have hcan : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      ((@derivedInterchangeFamily Λ _ _) k i r p h).hom =
        Functor.rightDerivedFunctorPlusBaseChange ((@ordinaryInterchange Λ _) k i r p h).hom := by
    intro A B C D k i r p _ _ _ _ h
    rfl
  generalize hd : (@ordinaryInterchange Λ _) = δ at hδ hcan
  generalize hg : (@derivedInterchangeFamily Λ _ _) = γ at hcan
  obtain ⟨hr, hb⟩ := properOpenInterchangeGeometricNormalization_of_normalization Λ δ γ hδ hcan
  refine ⟨δ, γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B C D k i r p _ _ _ _ h F
    exact hδ k i r p h F
  · intro A B C D k i r p _ _ _ _ h J
    exact normalized_base_change_unit (lowerStar (ModuleCat.{u + 1} Λ) r)
      (lowerStar (ModuleCat.{u + 1} Λ) p)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) (δ k i r p h).hom
      (γ k i r p h).hom (hcan k i r p h) J
  · exact hr
  · intro A B C D E F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ h₁ h₂ h K
    exact generic_vertical_pasting
      (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar (ModuleCat.{u + 1} Λ) r₂)
      (lowerStar (ModuleCat.{u + 1} Λ) (r₁ ≫ r₂))
      (lowerStar (ModuleCat.{u + 1} Λ) p₁) (lowerStar (ModuleCat.{u + 1} Λ) p₂)
      (lowerStar (ModuleCat.{u + 1} Λ) (p₁ ≫ p₂))
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
      (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)
      (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)
      (δ k i r₁ p₁ h₁).hom (δ i j r₂ p₂ h₂).hom
      (δ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom
      (ordinary_vertical Λ δ hδ k i j r₁ r₂ p₁ p₂ h₁ h₂ h)
      (γ k i r₁ p₁ h₁).hom (γ i j r₂ p₂ h₂).hom
      (γ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom
      (hcan k i r₁ p₁ h₁) (hcan i j r₂ p₂ h₂)
      (hcan k j (r₁ ≫ r₂) (p₁ ≫ p₂) h) K
  · exact @properOpenInterchangeHorizontalPasting_of_normalization Λ _ _ δ γ hδ hcan
  · intro A B k _ K
    let h := (Category.comp_id k).trans (Category.id_comp k).symm
    exact derived_vertical_identity
      (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A))
      (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
      (lowerStarId (ModuleCat.{u + 1} Λ) A)
      (lowerStarId (ModuleCat.{u + 1} Λ) B)
      (δ k k (𝟙 A) (𝟙 B) h).hom (γ k k (𝟙 A) (𝟙 B) h).hom
      (ordinary_identity_vertical Λ k (δ k k (𝟙 A) (𝟙 B) h)
        (hδ k k (𝟙 A) (𝟙 B) h))
      (hcan k k (𝟙 A) (𝟙 B) h)
      (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).hom
      (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).hom
      (lowerStarIdDerivedPlus_hom_app_fac (ModuleCat.{u + 1} Λ) A)
      (lowerStarIdDerivedPlus_hom_app_fac (ModuleCat.{u + 1} Λ) B) K
  · intro A C r _ K
    let h := (Category.id_comp r).trans (Category.comp_id r).symm
    exact derived_horizontal_identity (lowerStar (ModuleCat.{u + 1} Λ) r)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 A))
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 C))
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A))
        (upperStarId (ModuleCat.{u + 1} Λ) A))
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C))
        (upperStarId (ModuleCat.{u + 1} Λ) C))
      (δ (𝟙 A) (𝟙 C) r r h) (γ (𝟙 A) (𝟙 C) r r h)
      (ordinary_identity_horizontal Λ r (δ (𝟙 A) (𝟙 C) r r h)
        (hδ (𝟙 A) (𝟙 C) r r h))
      (hcan (𝟙 A) (𝟙 C) r r h) K
  · exact hb

end AlgebraicGeometry.Etale
