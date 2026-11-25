/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import all WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
import all WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all WeilConjectures.CategoryTheory.Strict.StrictRoosShiftLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.Basic.Denumerable
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility

/-! # Product-preserving exact functors commute with the specified derived-limit mate

## References

* Stacks Tags 0940, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] WeilConjectures.sfAbBijective
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
private def productLimitCochainUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  derivedCochainRightUnit (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
private theorem productLimitCochainUnit_eq (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (X : CochainComplex (ℕᵒᵖ ⥤ reductionModules T R) ℤ) :
    (productLimitCochainUnit T R).app X = chainDerivedUnit (completedTowerLimit T R) X := by
  unfold productLimitCochainUnit
  rw [cochainRightUnit_app_eq]
  dsimp only [chainDerivedUnit]
  simp only [quotient_hom_id, quotient_inv_id, Category.id_comp]
  erw [(completedTowerLimit T R).rightDerivedFunctor.map_id, Category.comp_id]
  rfl

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
private def productLimitRoosUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ completedRlim T R :=
  (Functor.isoWhiskerRight
    (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
    DerivedCategory.Q).inv ≫ productLimitCochainUnit T R

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
private theorem productLimitRoosUnit_derived (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (completedRlim T R).IsRightDerivedFunctor (productLimitRoosUnit T R)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ reductionModules T R) (.up ℤ)) := by
  have : (completedRlim T R).IsRightDerivedFunctor (completedRlimUnit T R)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    dsimp only [completedRlim, completedRlimUnit]
    infer_instance
  have h := cochainRightUnit_universal (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).mpr
  exact (Functor.isLeftKanExtension_iff_of_iso₂
    (productLimitCochainUnit T R) (productLimitRoosUnit T R)
    (Functor.isoWhiskerRight
      (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
      DerivedCategory.Q) (Iso.refl _) (by
        dsimp only [productLimitRoosUnit, Iso.refl_hom]
        rw [Functor.whiskerLeft_id', Category.comp_id,
          ← Category.assoc, Iso.hom_inv_id, Category.id_comp])).mp h

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
private theorem productLimitRoos_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (LA : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory C)
    (LB : DerivedCategory (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory D)
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB)
    (hnorm : CbcLimitNormalized F LA LB
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    ∀ X : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      F.mapDerivedCategory.map (uA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (preservesLimitNatIso F (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
        uB.app ((((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex
          (.up ℤ)).obj X) := by
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  intro X
  let Y :=
    (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)).obj X
  let iA := CategoryTheory.StrictRoosShiftProof.limitModelPointIso X
  let iB := CategoryTheory.StrictRoosShiftProof.limitModelPointIso Y
  let beta := limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone
    (limit.cone X.asFunctor))
  have hi : (F.mapHomologicalComplex (.up ℤ)).map iA.hom ≫ beta =
      (NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom := by
    apply limit.hom_ext
    intro n
    dsimp only [beta]
    rw [Category.assoc, limit.lift_π]
    dsimp only [Functor.mapCone, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [← Functor.map_comp,
      CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π,
      Category.assoc, CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π]
    apply HomologicalComplex.Hom.ext
    funext q
    change F.map (limit.π (X.X q) n) =
      (preservesLimitIso F (X.X q)).hom ≫ limit.π _ n
    exact (preservesLimitIso_hom_π F (X.X q) n).symm
  have hh := congrArg (fun z ↦ F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫ z)
    (hnorm.equation X)
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc, Functor.map_comp] at hh
  change F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫
    F.mapDerivedCategory.map (DerivedCategory.Q.map iA.inv) ≫ _ = _ at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  erw [F.mapDerivedCategoryFactors_hom_naturality_assoc] at hh
  simp only [← DerivedCategory.Q.map_comp_assoc] at hh
  erw [reassoc_of% hi] at hh
  change _ = _ ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom ≫ iB.inv) ≫ _ at hh
  simp only [Iso.hom_inv_id, Category.comp_id] at hh
  exact hh

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
/-- The canonical constant-tower mate is invertible for an exact module functor
preserving countable products. -/
theorem productPreservingDerivedLimitMate_isIso {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)]
    (hphi : ∀ N : ℕ → reductionModules T R, IsIso (piComparison F N)) :
    IsIso (mateEquiv
      (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _) ⊣
        completedTowerLimit T R).mapDerivedCategoryRightDerivedAdjunction
      (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules S R' ⥤ _) ⊣
        completedTowerLimit S R').mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (Functor.compConstIso ℕᵒᵖ F)).hom)) := by
  have := ambient_exact T R
  have := ambient_exact S R'
  have : PreservesLimitsOfShape (Discrete ℕ) F := natProducts F hphi
  have : PreservesLimitsOfShape ℕᵒᵖ F := natProducts_preservesTowers F
  obtain ⟨a, _⟩ := CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology T) (reductionModuleRing T R) (completedRlim T R) (productLimitRoosUnit T R)
      (productLimitRoosUnit_derived T R)
  obtain ⟨b, _⟩ := CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology S) (reductionModuleRing S R') (completedRlim S R')
      (productLimitRoosUnit S R') (productLimitRoosUnit_derived S R')
  obtain ⟨c, _⟩ := CategoryTheory.NormalizedLimitSquare.comparisonData a b F hphi
  have hn := CategoryTheory.comparison_normalized F a b c
  have he := productLimitRoos_normalization F (completedRlim T R) (completedRlim S R')
    (productLimitCochainUnit T R) (productLimitCochainUnit S R') c.lambda hn
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules S R' ⥤ _) ⊣ lim)
  let s := Functor.compConstIso ℕᵒᵖ F
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  have hm : (mateEquiv aa bb (TwoSquare.mk _ _ _ _ s.hom)) = tau.hom := by
    apply NatTrans.ext
    funext M
    apply limit.hom_ext
    intro n
    have h := congrArg (fun z ↦ z.app n)
      (mateEquiv_counit aa bb (TwoSquare.mk _ _ _ _ s.hom) M)
    change (mateEquiv aa bb (TwoSquare.mk _ _ _ _ s.hom)).app M ≫
      limit.π _ n = _ at h
    exact h.trans (preservesLimitIso_hom_π F M n).symm
  have heq : c.lambda.hom = (mateEquiv
      aa.mapDerivedCategoryRightDerivedAdjunction bb.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)) := by
    apply derived_comp_ext (completedTowerLimit T R) F
      (cbcTowerDerived F ⋙ completedRlim S R')
    intro K
    apply (cancel_mono ((completedRlim S R').map
      ((cbcTowerFactors F).hom.app K))).mp
    have hh := derived_mate_factors aa bb s K
    rw [hm] at hh
    have he' := he K
    simp only [productLimitCochainUnit_eq] at he'
    simpa only [Category.assoc, Functor.mapDerivedCategorySquareIso] using he'.trans hh.symm
  rw [← heq]
  infer_instance

end AlgebraicGeometry.Scheme
