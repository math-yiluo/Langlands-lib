/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.SmoothPurity.ClopenMateComposite
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedComplexUnitCompatibility
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
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Proper-support normalization of the finite etale clopen mate

Source: Stacks Project, More on Etale Cohomology, Tag 0F7B,
first paragraph of the proof of lemma-shriek-proper-and-open
(blueprint: lem-cbc-etale-clopen-mate-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
namespace ClopenMateNormalization

section DerivedMate

open CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- Exact localization of a natural-transformation square, retaining the canonical
composition comparisons. Source: Stacks Tags 015F and 070K
(blueprint: def-cbc-localized-clopen-square). -/
@[no_expose, irreducible] def clopenLocalizedSquare (σ : G ⋙ L' ⟶ L ⋙ G') :
    G.mapDerivedCategory ⋙ L'.mapDerivedCategory ⟶
      L.mapDerivedCategory ⋙ G'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso G L').hom ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso C₂ (.up ℤ)) _ _ _ _
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex σ (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso L G').inv

omit [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃] in
private theorem clopenLocalizedSquare_fac (σ : G ⋙ L' ⟶ L ⋙ G')
    (K : CochainComplex C₂ ℤ) :
    (clopenLocalizedSquare σ).app (DerivedCategory.Q.obj K) ≫
        G'.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        G'.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac G L' K
  have h₂ := Functor.mapDerivedCategoryCompIso_fac L G' K
  simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_hom,
    NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at h₁ h₂
  erw [DerivedCategory.Q.map_id, Category.comp_id] at h₁ h₂
  simp only [clopenLocalizedSquare, NatTrans.comp_app, Category.assoc]
  erw [h₂]
  simp only [Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc]
  change _ ≫ ((G ⋙ L').mapDerivedCategoryFactors.hom.app K ≫ _) = _
  erw [← reassoc_of% h₁]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

omit [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃] in
private theorem clopenLocalizedSquare_fach (σ : G ⋙ L' ⟶ L ⋙ G')
    (K : HomotopyCategory C₂ (.up ℤ)) :
    (clopenLocalizedSquare σ).app (DerivedCategory.Qh.obj K) ≫
        G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
        G'.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hG' : G'.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C₂ (.up ℤ)).obj K)) =
      G'.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        G'.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso C₃).inv.app _ ≫
        DerivedCategory.Qh.map ((G'.mapHomotopyCategoryFactors (.up ℤ)).inv.app
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) :=
    G'.mapDerivedCategoryFactorsh_hom_app _
  have hL' : L'.mapDerivedCategoryFactorsh.hom.app
      ((G.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C₂ (.up ℤ)).obj K)) =
      L'.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₄).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        L'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso C₃).inv.app _ ≫
        DerivedCategory.Qh.map ((L'.mapHomotopyCategoryFactors (.up ℤ)).inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj K)) :=
    L'.mapDerivedCategoryFactorsh_hom_app _
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, hG',
    Functor.mapDerivedCategoryFactorsh_hom_app, hL']
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
    cancelIso, Category.comp_id]
  rw [← CategoryTheory.Functor.comp_map L.mapDerivedCategory G'.mapDerivedCategory,
    ← NatTrans.naturality_assoc]
  erw [reassoc_of% clopenLocalizedSquare_fac σ K]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality]
  rfl

section Plus
variable [EnoughInjectives C₁] [EnoughInjectives C₃]

/-- Exact localization of a natural-transformation square, retaining the canonical
composition comparisons. Source: Stacks Tags 015F and 070K
(blueprint: def-cbc-localized-clopen-square). -/
@[no_expose, irreducible] def clopenLocalizedSquarePlus (σ : G ⋙ L' ⟶ L ⋙ G') :
    G.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus ⟶
      L.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus :=
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂)
      ((G ⋙ L').mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (G ⋙ L').mapDerivedCategoryPlus := ⟨(G ⋙ L').mapDerivedCategoryPlusFactorsh⟩
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂)
      ((L ⋙ G').mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (L ⋙ G').mapDerivedCategoryPlus := ⟨(L ⋙ G').mapDerivedCategoryPlusFactorsh⟩
  (Functor.mapDerivedCategoryPlusCompIso G L').inv ≫
    Localization.liftNatTrans DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂) _ _ _ _
      (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus σ) DerivedCategory.Plus.Qh) ≫
    (Functor.mapDerivedCategoryPlusCompIso L G').hom

omit [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
  [EnoughInjectives C₁] [EnoughInjectives C₃] in
private theorem clopenLocalizedSquarePlus_fac (σ : G ⋙ L' ⟶ L ⋙ G')
    (K : HomotopyCategory.Plus C₂) :
    (clopenLocalizedSquarePlus σ).app (DerivedCategory.Plus.Qh.obj K) ≫
        G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app K) := by
  have h₁ := Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh G L' K
  have h₂ := Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh L G' K
  simp only [clopenLocalizedSquarePlus, NatTrans.comp_app, Category.assoc]
  erw [h₂]
  simp only [Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc]
  erw [← reassoc_of% h₁]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

omit [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
  [EnoughInjectives C₁] [EnoughInjectives C₃] in
/-- Component factorization of the exact localized square. This exposes the
normalization of the constructed map without exposing its implementation.
Source: Stacks Tags 015F and 070K
(blueprint: def-cbc-localized-clopen-square). -/
theorem clopenLocalizedSquarePlus_factorization (σ : G ⋙ L' ⟶ L ⋙ G')
    (K : HomotopyCategory.Plus C₂) :
    (clopenLocalizedSquarePlus σ).app (DerivedCategory.Plus.Qh.obj K) ≫
        G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app K) := by
  exact clopenLocalizedSquarePlus_fac σ K

end Plus

section Ambient
variable [EnoughInjectives C₁] [EnoughInjectives C₃]

private theorem mate_ambient (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G') :
    ∀ X : DerivedCategory.Plus C₁,
      DerivedCategory.Plus.ι.map
          ((mateEquiv adj.derivedPlus adj'.derivedPlus
            (TwoSquare.mk _ _ _ _ (clopenLocalizedSquarePlus σ))).app X) ≫
        R'.rightDerivedFunctorPlusCompatibility.hom.app (G'.mapDerivedCategoryPlus.obj X) =
      G.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app X) ≫
        (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (clopenLocalizedSquare σ))).app
            (DerivedCategory.Plus.ι.obj X) := by
  let gammaPlus := (mateEquiv adj.derivedPlus adj'.derivedPlus
    (TwoSquare.mk _ _ _ _ (clopenLocalizedSquarePlus σ)))
  let γ := (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (clopenLocalizedSquare σ)))
  let a : (R.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) ⋙ G.mapDerivedCategory ⟶
      G'.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R'.rightDerivedFunctor :=
    Functor.whiskerRight gammaPlus DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft G'.mapDerivedCategoryPlus R'.rightDerivedFunctorPlusCompatibility.hom
  let b : (R.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) ⋙ G.mapDerivedCategory ⟶
      G'.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R'.rightDerivedFunctor :=
    Functor.whiskerRight R.rightDerivedFunctorPlusCompatibility.hom G.mapDerivedCategory ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι γ
  have hab : a = b := by
    apply Functor.rightDerived_ext
      (R.rightDerivedFunctorPlus ⋙ (DerivedCategory.Plus.ι ⋙ G.mapDerivedCategory))
      (Functor.whiskerRight R.rightDerivedFunctorPlusUnith
          (DerivedCategory.Plus.ι ⋙ G.mapDerivedCategory) ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso C₁)
    apply NatTrans.ext
    funext K
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      CategoryTheory.Functor.comp_map, Category.id_comp, Category.assoc]
    have hp := Adjunction.derivedPlus_mateEquiv_app_fac adj adj' σ
      (TwoSquare.mk _ _ _ _ (clopenLocalizedSquarePlus σ))
      (clopenLocalizedSquarePlus_fac σ) K
    have hu := Adjunction.derivedExact_mateEquiv_app_fac adj adj' σ
      (TwoSquare.mk _ _ _ _ (clopenLocalizedSquare σ))
      (clopenLocalizedSquare_fach σ) ((HomotopyCategory.Plus.ι C₁).obj K)
    change G.mapDerivedCategoryPlus.map _ ≫ gammaPlus.app _ = _ at hp
    change G.mapDerivedCategory.map _ ≫ γ.app _ = _ at hu
    erw [← G.mapDerivedCategory.map_comp_assoc,
      (derivedComplexUnitCompatibility (C := C₁) (D := C₂)).2.2.2 R K]
    erw [hu]
    change DerivedCategory.Plus.ι.map
        (G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app K)) ≫
      DerivedCategory.Plus.ι.map (gammaPlus.app (DerivedCategory.Plus.Qh.obj K)) ≫ _ = _
    rw [← DerivedCategory.Plus.ι.map_comp_assoc, hp]
    simp only [DerivedCategory.Plus.ι.map_comp, Category.assoc]
    have hn := R'.rightDerivedFunctorPlusCompatibility.hom.naturality
      (G'.mapDerivedCategoryPlusFactorsh.inv.app K)
    simp only [CategoryTheory.Functor.comp_map] at hn
    erw [hn,
      reassoc_of% ((derivedComplexUnitCompatibility (C := C₃) (D := C₄)).2.2.2
        R' (G'.mapHomotopyCategoryPlus.obj K))]
    have hi : DerivedCategory.Plus.ι.map
        (G'.mapDerivedCategoryPlusFactorsh.inv.app K) =
      G'.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.Plus.ι C₁).obj K) := by
      apply (cancel_mono (G'.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.Plus.ι C₁).obj K))).1
      erw [← G'.ι_map_mapDerivedCategoryPlusFactorsh_hom_app K,
        ← DerivedCategory.Plus.ι.map_comp, Iso.inv_hom_id_app,
        DerivedCategory.Plus.ι.map_id]
      rw [G'.ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
      exact (G'.mapDerivedCategoryFactorsh.inv_hom_id_app
        ((HomotopyCategory.Plus.ι C₁).obj K)).symm
    simp only [Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app, hi]
    rfl
  intro X
  exact congr_app hab X

omit [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃] in
private theorem plus_mate_eq (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategoryPlus L.mapDerivedCategoryPlus
      L'.mapDerivedCategoryPlus G'.mapDerivedCategoryPlus)
    (hθ : ∀ K : HomotopyCategory.Plus C₂,
      θ.app (DerivedCategory.Plus.Qh.obj K) ≫
          G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
          G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
        L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
          L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app K))
    (δ : R ⋙ G ⟶ G' ⋙ R')
    (γ : R.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus ⟶
      G'.mapDerivedCategoryPlus ⋙ R'.rightDerivedFunctorPlus)
    (hδ : (mateEquiv adj adj' σ) = δ)
    (hγ : ∀ K : HomotopyCategory.Plus C₁,
      G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app K) ≫
          γ.app (DerivedCategory.Plus.Qh.obj K) =
        G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus δ).app K) ≫
          R'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
          R'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlusFactorsh.inv.app K)) :
    (mateEquiv adj.derivedPlus adj'.derivedPlus θ) = γ := by
  apply Functor.rightDerived_ext (R.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus)
    (Functor.whiskerRight R.rightDerivedFunctorPlusUnith G.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso C₁)
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id]
  rw [Adjunction.derivedPlus_mateEquiv_app_fac adj adj' σ θ hθ K, hδ]
  exact (hγ K).symm

end Ambient

end DerivedMate

variable (Λ : Type (u + 1)) [CommRing Λ]

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  upperStarLowerStarAdjunction openImmersionLowerShriekUpperStarAdjunction

/-- The lift to the cartesian open is clopen.
Source: Stacks Tags 01JY, 01W4, 01W6 and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization).
Proof: its square with k and the open projection is cartesian since i is monic.
Thus the lift is open. The projection to S is proper, hence separated, and its
composite with the lift is r, which is proper. Proper-over-separated makes the
lift proper. An open proper immersion is a closed immersion. -/
theorem lift_clopen {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    IsOpenImmersion (pullback.lift k r h) ∧ IsClosedImmersion (pullback.lift k r h) := by
  have hopen : IsOpenImmersion (pullback.lift k r h) := by
    have : IsOpenImmersion (pullback.lift k r h ≫ pullback.fst p i) := by
      simpa only [pullback.lift_fst] using (inferInstance : IsOpenImmersion k)
    exact IsOpenImmersion.of_comp _ (pullback.fst p i)
  have hproper : IsProper (pullback.lift k r h) := by
    have : IsProper (pullback.lift k r h ≫ pullback.snd p i) := by
      simpa only [pullback.lift_snd] using (inferInstance : IsProper r)
    exact IsProper.of_comp _ (pullback.snd p i)
  exact ⟨hopen, IsClosedImmersion.of_isPreimmersion _
    ((pullback.lift k r h).isClosedMap.isClosed_range)⟩

/-- Identity on a clopen component and zero on its complement: the ordinary
inverse-image/direct-image unit, transported through the canonical support inclusion.
Source: Stacks Tags 03S5, 0F51 and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
def projection {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⟶
      upperStar (ModuleCat.{u + 1} Λ) s ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit ≫
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) s)
      (@inv _ _ _ _ (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s)
        (isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
          (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_restrict {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) s).map ((projection Λ s).app F) =
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) s).obj F) := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  apply (cancel_mono
    ((upperStar (ModuleCat.{u + 1} Λ) s).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s).app
          ((upperStar (ModuleCat.{u + 1} Λ) s).obj F)) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).counit.app _)).1
  rw [unit_map_openImmersionLowerShriekToLowerStar_app_counit]
  simp only [projection, NatTrans.comp_app, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [NatIso.isIso_inv_app]
  simp only [CategoryTheory.Functor.map_inv, IsIso.inv_hom_id_assoc]
  exact (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).left_triangle_components F

/-- Transport of open extension along equality of its scheme morphism.
Source: Stacks Tag 03S5 (blueprint: lem-cbc-etale-clopen-mate-normalization). -/
def openCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (e : f = g) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) f ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) g := by
  subst g
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_comp_unit {U X Y : Scheme.{u}}
    (s : U ⟶ X) (b : X ⟶ Y) [IsOpenImmersion s] [IsOpenImmersion b]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit.app F ≫
        (upperStar (ModuleCat.{u + 1} Λ) s).map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b).unit.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).obj F)) ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) s b).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).obj F)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) (s ≫ b)).map
          ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv.app F) =
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) (s ≫ b)).unit.app F := by
  have hc := Adjunction.unit_leftAdjointUniq_hom_app
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (s ≫ b))
    (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b)).ofNatIsoRight
      (upperStarComp (ModuleCat.{u + 1} Λ) s b).symm) F
  change _ ≫ (upperStar (ModuleCat.{u + 1} Λ) (s ≫ b)).map
    ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).hom.app F) = _ at hc
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom] at hc
  rw [← reassoc_of% hc]
  simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem upper_comp_transport {V P S : Scheme.{u}}
    (s : V ⟶ P) (q : P ⟶ S) (r : V ⟶ S) (hr : s ≫ q = r) :
    (upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
        (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) hr)).hom =
      (upperStarComp (ModuleCat.{u + 1} Λ) s q r hr.symm).inv := by
  subst r
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_comp_unit_transport {V P W : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (k : V ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (hk : s ≫ b = k)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit.app F ≫
        (upperStar (ModuleCat.{u + 1} Λ) s).map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b).unit.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).obj F)) ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) s b k hk.symm).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).obj F)) ≫
        (upperStar (ModuleCat.{u + 1} Λ) k).map
          ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv.app F ≫
            (openCongr Λ hk).hom.app F) =
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) k).unit.app F := by
  subst k
  simpa only [openCongr, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
    open_comp_unit Λ s b F

/-- The prescribed composite of cartesian open base change, the clopen projection,
and the canonical open-extension and inverse-image compositors.
Source: Stacks Tag 0F7B, first proof paragraph
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  let s := pullback.lift k r h
  letI := (lift_clopen k r p i h).1
  letI := (lift_clopen k r p i h).2
  let q := pullback.snd p i
  let b := pullback.fst p i
  CategoryTheory.clopenMateComposite
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) q)
    (upperStar (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv
    (projection Λ s)
    ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
      (openCongr Λ (pullback.lift_fst k r h)).hom)
    ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
      (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ))
        (pullback.lift_snd k r h))).hom)

/-- The prescribed sheaf alpha, expressed using its four defining factors.
Source: Stacks Tag 0F7B, first proof paragraph
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
theorem alpha_app {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (alpha Λ k r p i h).app F =
      let s := pullback.lift k r h
      letI := (lift_clopen k r p i h).1
      letI := (lift_clopen k r p i h).2
      let q := pullback.snd p i
      let b := pullback.fst p i
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv.app F ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).map
        ((projection Λ s).app ((upperStar (ModuleCat.{u + 1} Λ) q).obj F)) ≫
      ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
        (openCongr Λ (pullback.lift_fst k r h)).hom).app
          ((upperStar (ModuleCat.{u + 1} Λ) s).obj
            ((upperStar (ModuleCat.{u + 1} Λ) q).obj F)) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
        (((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
          (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ))
            (pullback.lift_snd k r h))).hom).app F) := by
  let s := pullback.lift k r h
  let := (lift_clopen k r p i h).1
  let := (lift_clopen k r p i h).2
  let q := pullback.snd p i
  let b := pullback.fst p i
  exact CategoryTheory.clopenMateComposite_app
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) q)
    (upperStar (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv
    (projection Λ s)
    ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
      (openCongr Λ (pullback.lift_fst k r h)).hom)
    ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
      (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ))
        (pullback.lift_snd k r h))).hom) F

private lemma map_iso_cancel {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {X Y : A} (e : X ≅ Y) {Z : B} (d : Z ≅ F.obj Y) :
    d.hom ≫ F.map e.inv ≫ F.map e.hom ≫ d.inv = 𝟙 Z := by
  rw [← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp, d.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem lift_square_comp {V P W S T : Scheme.{u}}
    (s : V ⟶ P) (b : P ⟶ W) (q : P ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (k : V ⟶ W) (r : V ⟶ S) (hk : k = s ≫ b) (hr : r = s ≫ q)
    (hbq : b ≫ p = q ≫ i) (h : k ≫ p = r ≫ i)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarComp (ModuleCat.{u + 1} Λ) s q r hr).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) i).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) s).map
        ((squareUpperStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk hbq)).hom.app F) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) s b k hk).inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) p).obj F) =
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk h)).hom.app F := by
  simp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [upperStarComp_hom_app_map_upperStarComp_inv_app_assoc
    (ModuleCat.{u + 1} Λ) s q i r (b ≫ p) (k ≫ p) hr hbq h F]
  have hc := upperStarComp_hom_app_map_upperStarComp_inv_app
    (ModuleCat.{u + 1} Λ) s b p k (b ≫ p) (k ≫ p) hk rfl rfl F
  have hc' : (upperStarComp (ModuleCat.{u + 1} Λ) s (b ≫ p) (k ≫ p)
        (by rw [hk, Category.assoc])).hom.app F ≫
      (upperStar (ModuleCat.{u + 1} Λ) s).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) b p).hom.app F) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) s b k hk).inv.app _ =
      (upperStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F := by
    apply (cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) k p).inv.app F)).1
    rw [← reassoc_of% hc]
    exact (map_iso_cancel (upperStar (ModuleCat.{u + 1} Λ) s)
      ((upperStarComp (ModuleCat.{u + 1} Λ) b p).app F)
      ((upperStarComp (ModuleCat.{u + 1} Λ) s b k hk).app
        ((upperStar (ModuleCat.{u + 1} Λ) p).obj F))).trans
      ((upperStarComp (ModuleCat.{u + 1} Λ) k p).inv_hom_id_app F).symm
  rw [hc']

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem factor_unit
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E]
    (Gs : B ⥤ C) (Gb : D ⥤ B) (Gq : A ⥤ B) (Gp : E ⥤ D)
    (Gi : E ⥤ A) (Gk : D ⥤ C) (Gr : A ⥤ C)
    (Jb : B ⥤ D) (Ji : A ⥤ E) (Js : C ⥤ B) (Jk : C ⥤ D)
    (ηi : 𝟭 A ⟶ Ji ⋙ Gi) (ηb : 𝟭 B ⟶ Jb ⋙ Gb)
    (ηs : 𝟭 C ⟶ Js ⋙ Gs) (ηk : 𝟭 C ⟶ Jk ⋙ Gk)
    (κr : Gr ≅ Gq ⋙ Gs) (κk : Gk ≅ Gb ⋙ Gs)
    (a : Gi ⋙ Gr ≅ Gp ⋙ Gk) (b : Gi ⋙ Gq ≅ Gp ⋙ Gb)
    (β : Gq ⋙ Jb ≅ Ji ⋙ Gp) (π : 𝟭 B ⟶ Gs ⋙ Js)
    (c : Js ⋙ Jb ⟶ Jk)
    (ha : ∀ F, κr.hom.app (Gi.obj F) ≫ Gs.map (b.hom.app F) ≫
      κk.inv.app (Gp.obj F) = a.hom.app F)
    (hπ : ∀ F, Gs.map (π.app F) = ηs.app (Gs.obj F))
    (hc : ∀ F, ηs.app F ≫ Gs.map (ηb.app (Js.obj F)) ≫
      κk.inv.app (Jb.obj (Js.obj F)) ≫ Gk.map (c.app F) = ηk.app F)
    (hβ : ∀ F, ηb.app (Gq.obj F) ≫ Gb.map (β.hom.app F) =
      Gq.map (ηi.app F) ≫ b.hom.app (Ji.obj F)) (F : A) :
    Gr.map (ηi.app F) ≫ a.hom.app (Ji.obj F) ≫
      Gk.map (β.inv.app F ≫ Jb.map (π.app (Gq.obj F)) ≫
        c.app (Gs.obj (Gq.obj F)) ≫ Jk.map (κr.inv.app F)) =
      ηk.app (Gr.obj F) := by
  have hnat := κr.hom.naturality (ηi.app F)
  simp only [CategoryTheory.Functor.comp_map] at hnat
  rw [← ha]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
  rw [← κk.inv.naturality_assoc, ← κk.inv.naturality_assoc]
  simp only [CategoryTheory.Functor.comp_map]
  have hb : Gq.map (ηi.app F) ≫ b.hom.app _ ≫ Gb.map (β.inv.app F) =
      ηb.app (Gq.obj F) := by
    rw [← reassoc_of% hβ F]
    simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
    erw [Gb.map_id, Category.comp_id]
  rw [← Gs.map_comp_assoc, ← Gs.map_comp_assoc]
  simp only [Category.assoc]
  rw [hb]
  have hn := ηb.naturality (π.app (Gq.obj F))
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hn
  rw [← Gs.map_comp_assoc]
  erw [← hn]
  rw [Gs.map_comp, Category.assoc, hπ]
  erw [reassoc_of% hc]
  have ht := ηk.naturality (κr.inv.app F)
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at ht
  erw [← ht]
  exact κr.hom_inv_id_app_assoc F (ηk.app (Gr.obj F))

private theorem factor_unit_composite
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E]
    (Gs : B ⥤ C) (Gb : D ⥤ B) (Gq : A ⥤ B) (Gp : E ⥤ D)
    (Gi : E ⥤ A) (Gk : D ⥤ C) (Gr : A ⥤ C)
    (Jb : B ⥤ D) (Ji : A ⥤ E) (Js : C ⥤ B) (Jk : C ⥤ D)
    (ηi : 𝟭 A ⟶ Ji ⋙ Gi) (ηb : 𝟭 B ⟶ Jb ⋙ Gb)
    (ηs : 𝟭 C ⟶ Js ⋙ Gs) (ηk : 𝟭 C ⟶ Jk ⋙ Gk)
    (κr : Gr ≅ Gq ⋙ Gs) (κk : Gk ≅ Gb ⋙ Gs)
    (a : Gi ⋙ Gr ≅ Gp ⋙ Gk) (b : Gi ⋙ Gq ≅ Gp ⋙ Gb)
    (β : Gq ⋙ Jb ≅ Ji ⋙ Gp) (π : 𝟭 B ⟶ Gs ⋙ Js)
    (c : Js ⋙ Jb ⟶ Jk)
    (ha : ∀ F, κr.hom.app (Gi.obj F) ≫ Gs.map (b.hom.app F) ≫
      κk.inv.app (Gp.obj F) = a.hom.app F)
    (hπ : ∀ F, Gs.map (π.app F) = ηs.app (Gs.obj F))
    (hc : ∀ F, ηs.app F ≫ Gs.map (ηb.app (Js.obj F)) ≫
      κk.inv.app (Jb.obj (Js.obj F)) ≫ Gk.map (c.app F) = ηk.app F)
    (hβ : ∀ F, ηb.app (Gq.obj F) ≫ Gb.map (β.hom.app F) =
      Gq.map (ηi.app F) ≫ b.hom.app (Ji.obj F)) (d : Gq ⋙ Gs ⟶ Gr) (hd : d = κr.inv) (F : A) :
    Gr.map (ηi.app F) ≫ a.hom.app (Ji.obj F) ≫
      Gk.map ((CategoryTheory.clopenMateComposite Ji Gp Gq Gs Js Jb Jk Gr
        β.inv π c d).app F) = ηk.app (Gr.obj F) := by
  rw [CategoryTheory.clopenMateComposite_app, hd]
  exact factor_unit Gs Gb Gq Gp Gi Gk Gr Jb Ji Js Jk ηi ηb ηs ηk κr κk a b β π c
    ha hπ hc hβ F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem alpha_open_unit {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) r).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F) ≫
      (squareUpperStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk h)).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) k).map ((alpha Λ k r p i h).app F) =
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k).unit.app
      ((upperStar (ModuleCat.{u + 1} Λ) r).obj F) := by
  let s := pullback.lift k r h
  have := (lift_clopen k r p i h).1
  have := (lift_clopen k r p i h).2
  let b := pullback.fst p i
  let q := pullback.snd p i
  let hk := pullback.lift_fst k r h
  let hr := pullback.lift_snd k r h
  let hbq := pullback.condition (f := p) (g := i)
  let β := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
    (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)
  delta alpha
  exact factor_unit_composite
    (upperStar (ModuleCat.{u + 1} Λ) s)
    (upperStar (ModuleCat.{u + 1} Λ) b)
    (upperStar (ModuleCat.{u + 1} Λ) q)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) k)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i).unit
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b).unit
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k).unit
    (upperStarComp (ModuleCat.{u + 1} Λ) s q r hr.symm)
    (upperStarComp (ModuleCat.{u + 1} Λ) s b k hk.symm)
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk h))
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk hbq)) β (projection Λ s)
    ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
      (openCongr Λ hk).hom)
    (lift_square_comp Λ s b q p i k r hk.symm hr.symm hbq h)
    (projection_restrict Λ s)
    (by intro E; simpa only [NatTrans.comp_app] using
      open_comp_unit_transport Λ s b k hk E)
    (fun E ↦ unit_map_openImmersionLowerShriekBaseChangeMap_app
      (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip.toCommSq E)
    _ (upper_comp_transport Λ s q r (pullback.lift_snd k r h)) F

/-- The ordinary proper-adjunction mate of the specified clopen comparison.
Source: Stacks Tag 0F7B (blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def mate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) (alpha Λ k r p i h)

/-- Exact localization of the specified alpha, on the ordinary derived categories.
Source: Stacks Tags 015F and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def derivedAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategory :=
  clopenLocalizedSquare (alpha Λ k r p i h)

/-- Restriction of the exact localization of alpha to bounded-below objects.
Source: Stacks Tags 015F and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def derivedAlphaPlus {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus :=
  clopenLocalizedSquarePlus (alpha Λ k r p i h)

/-- The bounded-below alpha is the exact localized sheaf square.
Source: Stacks Tags 015F and 0F7B
(blueprint: def-cbc-etale-clopen-mate-normalization-data). -/
theorem derivedAlphaPlus_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    derivedAlphaPlus Λ k r p i h = clopenLocalizedSquarePlus (alpha Λ k r p i h) := by
  rfl

/-- The actual proper mate, using the unbounded derived adjunction induced by the
ordinary inverse-image/direct-image adjunction.
Source: Stacks Tags 0F7B and 070K
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def derivedMate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (derivedAlpha Λ k r p i h))

/-- The proper mate in D+, formed with the induced bounded-below adjunctions.
Source: Stacks Tags 0F7B and 015F
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
def derivedMatePlus {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).derivedPlus
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).derivedPlus
    (derivedAlphaPlus Λ k r p i h))

/-- The support-preserving comparison selected from the recorded coherence theorem.
Its inclusion into (ir)_* = (pk)_* retains every section, uniquely determining it.
Source: Stacks Tags 0F50, 0F51 and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def supportComparison [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  (properOpenInterchangeData Λ).underived k i r p h

/-- The named normalized finite comparison from the recorded coherence theorem.
Its derived-unit normalization uniquely determines its natural transformation.
Source: Stacks Tag 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
def normalizedComparison [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (properOpenInterchangeCoherence Λ).choose_spec.choose k i r p h

/-- The degreewise support identification, followed by the specified p_*t.
Source: Stacks Tag 0F7B, the displayed chain map in its first proof paragraph
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def resolutionArrow [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
        (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ⟶
      ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj I :=
  (NatTrans.mapHomologicalComplex (supportComparison Λ k r p i h).hom (.up ℤ)).app J ≫
  ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).map t

/-- The chain transpose alpha followed by the ordinary r-counit and the chosen t.
Source: Stacks Tag 0F7B and the termwise adjunction
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def transposeArrow {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((upperStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj
        (((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
          (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J)) ⟶ I :=
  (NatTrans.mapHomologicalComplex (alpha Λ k r p i h) (.up ℤ)).app
    (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ≫
  ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex (.up ℤ)).map
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex
      (.up ℤ)).counit.app J) ≫ t

/-- Canonical source identification between D+ and its fully faithful ambient category.
Source: Stacks Tags 015F, 070K (blueprint: lem-cbc-etale-clopen-mate-normalization). -/
def sourceCompatibility {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsOpenImmersion i]
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory.mapIso
    ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.app L)

/-- Canonical target identification between D+ and its fully faithful ambient category.
Source: Stacks Tags 015F, 070K (blueprint: lem-cbc-etale-clopen-mate-normalization). -/
def targetCompatibility {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k]
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L))

attribute [local irreducible] mate supportComparison normalizedComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem plus_normalized [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (hm : mate Λ k r p i h = (supportComparison Λ k r p i h).hom) :
    derivedMatePlus Λ k r p i h = (normalizedComparison Λ k r p i h).hom := by
  have hn : normalizedComparison Λ k r p i h =
      (properOpenInterchangeData Λ).derived k i r p h := by
    delta normalizedComparison
    exact (congrArg (fun γ : ProperOpenDerivedFamily Λ ↦ γ k i r p h)
      (properOpenInterchangeData_derived Λ)).symm
  rw [hn]
  apply plus_mate_eq
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (TwoSquare.mk _ _ _ _ (alpha Λ k r p i h))
    (TwoSquare.mk _ _ _ _ (derivedAlphaPlus Λ k r p i h))
    (by exact clopenLocalizedSquarePlus_fac (alpha Λ k r p i h))
    (supportComparison Λ k r p i h).hom
    ((properOpenInterchangeData Λ).derived k i r p h).hom
  · simpa only [mate, TwoSquare.mk] using hm
  · intro K
    delta supportComparison
    simpa only [rightDerivedLowerStarPlus] using
      (properOpenInterchangeData Λ).unitNormalization k i r p h K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem alpha_include {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    alpha Λ k r p i h ≫ Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) r)
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k) =
      Functor.whiskerRight
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i)
          (upperStar (ModuleCat.{u + 1} Λ) p) ≫
        baseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk h.symm) := by
  apply NatTrans.ext
  funext F
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) k).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [upperStar_map_baseChangeMap_app_counit]
  let η := (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F
  have : IsIso η := by
    dsimp only [η]
    rw [openImmersionLowerShriekUpperStarAdjunction_unit_app]
    infer_instance
  have : Epi
      ((upperStar (ModuleCat.{u + 1} Λ) r).map η ≫
        (squareUpperStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk h)).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj F)) :=
    IsIso.epi_of_iso _
  apply (cancel_epi ((upperStar (ModuleCat.{u + 1} Λ) r).map η ≫
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk h)).hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj F))).1
  simp only [Category.assoc]
  rw [reassoc_of% alpha_open_unit Λ k r p i h F,
    unit_map_openImmersionLowerShriekToLowerStar_app_counit]
  have hn := (squareUpperStarIso (ModuleCat.{u + 1} Λ)
    (CommSq.mk h.symm)).hom.naturality
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app F)
  simp only [CategoryTheory.Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [squareUpperStarIso_flip_hom_app_hom_app_assoc]
  rw [← (upperStar (ModuleCat.{u + 1} Λ) r).map_comp_assoc,
    ← (upperStar (ModuleCat.{u + 1} Λ) r).map_comp]
  simp only [η, Category.assoc]
  rw [unit_map_openImmersionLowerShriekToLowerStar_app_counit]
  erw [(upperStar (ModuleCat.{u + 1} Λ) r).map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_include {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    mate Λ k r p i h ≫ Functor.whiskerRight
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k)
        (lowerStar (ModuleCat.{u + 1} Λ) p) =
    Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} Λ) r)
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i) ≫
      (squareLowerStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk h.symm)).hom := by
  let sq := CommSq.mk h.symm
  let a := TwoSquare.mk _ _ _ _ (alpha Λ k r p i h)
  let b := baseChangeSquare (ModuleCat.{u + 1} Λ) sq
  have he : a.whiskerBottom
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k) =
    b.whiskerTop (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i) := by
    exact alpha_include Λ k r p i h
  have hm := congrArg
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)) he
  rw [mateEquiv_whiskerBottom] at hm
  have hb := mateEquiv_whiskerTop_whiskerBottom
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) b
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i) (𝟙 _)
  simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.comp_id] at hb
  rw [hb] at hm
  have hm' := hm
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight] at hm'
  dsimp only [b] at hm'
  have hmate := mateEquiv_baseChangeSquare (ModuleCat.{u + 1} Λ) sq
  change mateEquiv _ _ _ = _ at hmate
  rw [hmate] at hm'
  simpa only [mate, a, sq, TwoSquare.mk,
    Functor.whiskerLeft_id, Category.comp_id] using hm'

private theorem open_compare_mono {X Y : Scheme.{u}}
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

private lemma iso_change_middle {A : Type*} [Category* A] {X Y Z W : A}
    (a : Y ≅ Z) (b : X ≅ W) (e : Z ≅ W) :
    (b ≪≫ (a ≪≫ e).symm).hom ≫ a.hom = (b ≪≫ e.symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private lemma lower_square_comp {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) :
    (squareLowerStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk h.symm)).hom ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom =
      (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom := by
  unfold squareLowerStarIso
  rw [← lowerStarComp_trans_eqToIso (ModuleCat.{u + 1} Λ) k p (r ≫ i) h,
    ← lowerStarComp_trans_eqToIso (ModuleCat.{u + 1} Λ) r i (k ≫ p) h.symm]
  exact iso_change_middle _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_normalized_of_inclusion {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p)
    (hδ : ∀ F, δ.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p (k ≫ p) rfl).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F) :
    mate Λ k r p i h = δ := by
  apply NatTrans.ext
  funext F
  have := open_compare_mono Λ k F
  apply (cancel_mono
    ((lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F)).1
  rw [hδ]
  have hm := congr_app (mate_include Λ k r p i h) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  rw [← Category.assoc, hm]
  have hs := congr_app (lower_square_comp Λ k r p i h) F
  simp only [NatTrans.comp_app] at hs
  rw [Category.assoc, hs]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_normalized [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    mate Λ k r p i h = (supportComparison Λ k r p i h).hom := by
  apply ordinary_normalized_of_inclusion Λ k r p i h
  intro F
  unfold supportComparison
  exact (properOpenInterchangeData Λ).inclusionNormalization k i r p h F

/-- The underived mate is exactly the section-preserving proper-support identification;
the derived mate is the named normalized finite comparison and agrees with its ambient
unbounded construction. Quasi-compactness is required only as in the node, with no
cartesian assumption. The representative and transpose clauses are stated below.
Source: Stacks Tag 0F7B, first proof paragraph
(blueprint: lem-cbc-etale-clopen-mate-normalization).

Proof: (1) The lift is open by open base change and proper by proper-over-separated,
hence clopen. (2) The cartesian open comparison is the transpose of the open unit;
restricting it and the clopen projection along k gives identity under those units.
(3) Include the proper mate into p_*k_*F. Under the composite inverse-image
adjunction its transpose is the r-counit. The support identification has exactly
the same transpose because it preserves underlying sections. Cancel the monic
support inclusion to identify the maps. (4) Naturality gives degreewise equality
on complexes. (5) Exact inverse image and open extension descend through localization.
The derived adjunction is induced by the ordinary one: on K-injective targets its
counit is represented by the chain counit, by derived-counit compatibility and the
K-injective Hom bijection. (6) Naturality of that bijection in t gives the support
chain map followed by p_*t. (7) This is exactly the coherence theorem's normalized
finite comparison. The same argument includes r = identity and V = S. The canonical
D+ compatibility isomorphisms identify the two derived adjunctions and exact
localizations, proving the displayed ambient equation.
Dependencies: properSupportSheafComposition, derivedExtensionZeroBaseChangeUnderivedCompatibility,
etaleInverseImageModulesExact, exact-functor localization, termwise adjunction,
K-injective total derivation, preservation of K-injectives by right adjoints of
exact functors, the K-injective Hom bijection, derived-counit compatibility, and
properOpenInterchangeCoherence, as in steps 1--7 of the DAG proof. -/
theorem etaleClopenMateNormalization [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    mate Λ k r p i h = (supportComparison Λ k r p i h).hom ∧
    derivedMatePlus Λ k r p i h = (normalizedComparison Λ k r p i h).hom ∧
    ∀ L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.Plus.ι.map ((derivedMatePlus Λ k r p i h).app L) ≫
        (targetCompatibility Λ k p L).hom =
      (sourceCompatibility Λ r i L).hom ≫
        (derivedMate Λ k r p i h).app (DerivedCategory.Plus.ι.obj L) := by
  have hm := ordinary_normalized Λ k r p i h
  refine ⟨hm, plus_normalized Λ k r p i h hm, ?_⟩
  intro X
  have hα : derivedAlpha Λ k r p i h = clopenLocalizedSquare (alpha Λ k r p i h) := rfl
  have hAlphaPlus : derivedAlphaPlus Λ k r p i h =
      clopenLocalizedSquarePlus (alpha Λ k r p i h) := rfl
  have hx := mate_ambient
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (TwoSquare.mk _ _ _ _ (alpha Λ k r p i h)) X
  rw [← hα, ← hAlphaPlus] at hx
  change DerivedCategory.Plus.ι.map ((derivedMatePlus Λ k r p i h).app X) ≫ _ =
    _ ≫ (derivedMate Λ k r p i h).app (DerivedCategory.Plus.ι.obj X) at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] derivedMate derivedAlpha alpha
  resolutionArrow transposeArrow

end ClopenMateNormalization
end AlgebraicGeometry.Etale
