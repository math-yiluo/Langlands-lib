/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
public import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
public import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
public import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
public import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
public import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
public import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
public import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
public import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
public import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientFiltration
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
public import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
public import WeilConjectures.AlgebraicGeometry.ConstantDerivedNormalizationUniversal
public import WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.FiniteFreeConstantLocalLift
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalScalarHomologyIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
public import WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjection
public import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
public import WeilConjectures.CategoryTheory.ConstantModuleFlat
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
public import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
public import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
public import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import WeilConjectures.ConstructibleSheaf.InternalHom
public import WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
public import WeilConjectures.RingTheory.FiniteConeFreeModel
public import WeilConjectures.RingTheory.KoszulProjectiveResolution
public import WeilConjectures.RingTheory.NilpotentProjectiveComplexLift
public import WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero
public import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
public import WeilConjectures.RingTheory.PseudoCoherentIffAllM
public import WeilConjectures.RingTheory.RlimPerfectComplete
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedLowerStarDerivedLimit
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Completed integral constant models

(auxiliary; not a blueprint node).

Definitions and exact realization for the integral stratified-perfect characterization.
Source: Bhatt--Scholze, Propositions 6.6.11 and 6.8.11(3)
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

-- Universe-polymorphic `{max u (t + 1)}` sheafification instances get stuck on `{u + 1}` searches.
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective


namespace AlgebraicGeometry.Scheme

/-- The ordinary realization N ↦ A_T ⊗_A N, using the normalized coefficient comparison.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def integralConstantModule (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{u + 1} A ⥤
      pbcModules T (pbcAdicCompletion T d) :=
  completedKoszulConstant T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite } ⋙
    pbcRestrict (pbcCompletedComparison T d).inv

/-- Exactness of the ordinary completed-constant realization.
Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
(auxiliary; not a blueprint node).
Proof: constant module sheafification is exact. The completed ring is flat over
constant A by lem-weil-pbc-completed-constant-sheaf-reduction, since d is Noetherian.
Thus tensoring with it preserves finite limits and colimits. Restriction along the
normalized coefficient isomorphism is an exact equivalence. -/
theorem integralConstantModule_exact (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    PreservesFiniteLimits (integralConstantModule T d) ∧
      PreservesFiniteColimits (integralConstantModule T d) := by
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let K := adicLisseConstantModules T A
  let E := completedConstantExtension T (adicDatumScalar T dd)
  let R := pbcRestrict (pbcCompletedComparison T d).inv
  have hK : PreservesFiniteLimits K ∧ PreservesFiniteColimits K := by
    let P : ModuleCat.{u + 1} A ⥤
      _root_.PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
      siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
        PresheafOfModules.pushforward₀
          ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
          ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
    have hP : PreservesFiniteLimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsLimits _ _
        (fun X ↦ hc)⟩
    have hP' : PreservesFiniteColimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsColimits _ _
        (fun X ↦ hc)⟩
    let S : _root_.PresheafOfModules.{u + 1} ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ⥤ _ :=
      PresheafOfModules.sheafification (adicLisseConstantUnit T A)
    exact ⟨comp_preservesFiniteLimits P S, comp_preservesFiniteColimits P S⟩
  have hE : PreservesFiniteLimits E ∧ PreservesFiniteColimits E := by
    let := dd.toCompleteCoefficientDatum.noetherian
    have h := completed_constant_algebra_flat_quotients T dd.ideal
      _ (Iso.refl _) (adicDatumScalar T dd) (by
        intro n
        exact (adicDatumScalar_exists T dd).exists.choose_spec n)
    have he := (exactFunctor_iff E).1 h.2.1
    exact ⟨he.1, he.2⟩
  let := hK.1
  let := hK.2
  let := hE.1
  let := hE.2
  exact ⟨comp_preservesFiniteLimits (K ⋙ E) R,
    comp_preservesFiniteColimits (K ⋙ E) R⟩

/-- Additivity of completed-constant realization, inherited from its two factors.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
instance integralConstantModule_additive (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : (integralConstantModule T d).Additive :=
  letI := (integralConstantModule_exact T d).1
  Functor.additive_of_preserves_binary_products _

/-- The derived realization P ↦ A_T ⊗^L_A P, obtained by localizing the exact
ordinary constant-module realization. On bounded finite projective complexes this
is its termwise tensor realization.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def integralConstantDerived (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : completedConstantDerived (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategory

/-- Restrict a derived object first to a stratum and then to a covering site object.
The slice coefficient sheaf is the restriction of the actual inverse-image ring.
Source: Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 0997 and 0998
(auxiliary; not a blueprint node). -/
def integralLocalDerived {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    completedConstantDerived (SheafOfModules.{u + 1}
      (((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)).over U)) :=
  ringedSiteDerivedRestrictionOfUniverses
    ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U
    ((adicTowerPullback g R).obj K)

/-- Condition (ii): finite strata, on each a pro-etale covering sieve, and on each
cover member an actual perfect A-complex whose completed realization is K there.
IsPerfectRingComplex is the recorded bounded finite-projective notion.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def IsIntegralStratifiedPerfect (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
            @DerivedCategory.IsPerfectRingComplex A _
              (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P ∧
              Nonempty (integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U K ≅
                integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U
                  ((integralConstantDerived T d).obj P))

/-- The constructible integral sheaf condition: finite strata and locally the ordinary
completed realization of a finitely presented A-module, including the zero module.
Source: Bhatt--Scholze, Definition 6.8.10
(auxiliary; not a blueprint node). -/
def IsIntegralStratifiedFinitelyPresented (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (F : pbcModules T (pbcAdicCompletion T d)) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ N : ModuleCat.{u + 1} A, Module.FinitePresentation A N ∧
            Nonempty ((SheafOfModules.overFunctor _ U).obj
              ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj F) ≅
              (SheafOfModules.overFunctor _ U).obj
                ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj
                  ((integralConstantModule T d).obj N)))

end AlgebraicGeometry.Scheme
