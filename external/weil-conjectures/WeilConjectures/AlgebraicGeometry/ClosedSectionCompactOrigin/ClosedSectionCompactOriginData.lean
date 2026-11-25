/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
/-! # Canonical data for the closed-section compact-origin equation

The constant objects, proper and exact closed-image identifications, source maps and
retained witnesses are the existing data of lem-pur-closed-section-compact-origin.
This module separates their construction from the source-normalization theorem.
(blueprint: def-pur-closed-section-compact-origin-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ClosedSectionCompactOrigin

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Finiteness of the retained coefficient quotient and its standard size lift.
Source: def-pur-conventions, positive coefficient level
(blueprint: lem-pur-closed-section-compact-origin). -/
local instance coefficientFinite : Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  Finite.of_equiv P.Ring Equiv.ulift.symm

/-- The degree-zero etale coefficient unit, using the recorded constant sheaf.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def etaleUnit (T : Scheme.{u}) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
    (SupportedConstantNormalization.constant P.Coefficient false T)

/-- The degree-zero pro-etale coefficient unit on the same small site.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def proUnit (T : Scheme.{u}) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
    (SupportedConstantNormalization.constant P.Coefficient true T)

/-- The degree-zero closed direct image of the etale constant module.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def etaleSource {B X : Scheme.{u}} (s : B ⟶ X) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
    (SupportedConstantNormalization.supported P.Coefficient false s)

/-- The degree-zero closed direct image of the pro-etale constant module.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def proSource {B X : Scheme.{u}} (s : B ⟶ X) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
    (SupportedConstantNormalization.supported P.Coefficient true s)

/-- Chi is the actual scalar-preserving constant comparison, descended in degree zero.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def constantComparison (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (etaleUnit P T).obj ≅ (proUnit P T).obj :=
  ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
    T).mapDerivedCategorySingleFunctor 0).app _ ≪≫
  (DerivedCategory.singleFunctor _ 0).mapIso
    (SupportedConstantNormalization.compareUnit P.Coefficient T)

/-- Epsilon is the actual closed-constant counit mate, not a chosen isomorphism.
Source: blueprint Step 1; supported-constant normalization
(blueprint: lem-pur-closed-section-compact-origin). -/
def supportedComparison {B X : Scheme.{u}} (s : B ⟶ X) [IsClosedImmersion s] :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
      (etaleSource P s).obj ≅ (proSource P s).obj :=
  letI := (SupportedConstantNormalization.site_normalization P s).2.2.2.2.1
  ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
    X).mapDerivedCategorySingleFunctor 0).app _ ≪≫
  (DerivedCategory.singleFunctor _ 0).mapIso
    (asIso (SupportedConstantNormalization.gamma P.Coefficient s))

/-- Closed pro-etale direct image is exact by the recorded complementary-open theorem.
Source: Stacks Tag 09BM (blueprint: lem-pur-closed-section-compact-origin). -/
instance closedPushExact {B X : Scheme.{u}} (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι] :
    PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s) :=
  ProEtale.preservesFiniteColimits_lowerStar_of_isCompl s s.openComplement.ι
    (eq_compl_iff_isCompl.mp s.range_eq_compl_range_openComplement_ι)

/-- Properness, exactness and the single-complex comparison identify Rs_! with s_*.
Source: blueprint Step 1, identity/proper compactification
(blueprint: lem-pur-closed-section-compact-origin). -/
def etaleClosedIso {B X : Scheme.{u}} (s : B ⟶ X) [IsClosedImmersion s] :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) s).obj
      (etaleUnit P B) ≅ etaleSource P s :=
  DerivedCategory.Plus.ι.preimageIso
    ((Etale.rightDerivedLowerShriekPlusCompatibility
      (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      s).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s).mapDerivedCategorySingleFunctor 0).app _)

/-- The constant etale-origin object used to evaluate the published origin compositor.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def originUnit (T : Scheme.{u}) :=
  (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T).obj
    (etaleUnit P T)

/-- The pro-etale proper/exact closed-image identification, including chi at its input.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def proClosedIso {B X : Scheme.{u}} (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι] :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) s).obj
      (originUnit P B).obj ≅ (proSource P s).obj :=
  (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) s).mapIso
    (constantComparison P B) ≪≫
  (ProEtale.rightDerivedLowerShriekIsoOfIsProper
    (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
  (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      s).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
  ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s).mapDerivedCategorySingleFunctor 0).app _

/-- Sigma_e uses closed identification, the canonical compositor, fs=id and the identity
comparison, conjugated from the supplied compactification to the standing one.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def etaleSigma {B X : Scheme.{u}} (f : X ⟶ B) [QuasiCompact f]
    (c : Compactification f) (s : B ⟶ X) [IsClosedImmersion s] (hs : s ≫ f = 𝟙 B) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} P.Coefficient) c).obj (etaleSource P s) ≅ etaleUnit P B :=
  letI := c.hasCompactification
  letI : HasCompactification (s ≫ f) := HasCompactification.of_eq hs.symm
  (Etale.rightDerivedLowerShriekOfCompactificationPlusIso P.Coefficient c
    (HasCompactification.compactification f)).app _ ≪≫
  (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) f).mapIso
    (etaleClosedIso P s).symm ≪≫
  (Etale.rightDerivedLowerShriekPlusCompIso P.Coefficient s f).app _ ≪≫
  (Etale.rightDerivedLowerShriekPlusCongr P.Coefficient hs).app _ ≪≫
  (Etale.rightDerivedLowerShriekPlusId P.Coefficient B).app _

/-- Sigma_p uses the specified origin compositor and identity comparison, with the same
chosen compactification c. Only canonical compactification comparisons intervene.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def proSigma {B X : Scheme.{u}} (f : X ⟶ B) [QuasiCompact f]
    (c : Compactification f) (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι] (hs : s ≫ f = 𝟙 B) :
    (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj (proSource P s).obj ≅ (proUnit P B).obj :=
  letI := c.hasCompactification
  letI : HasCompactification (s ≫ f) := HasCompactification.of_eq hs.symm
  (ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) c).mapIso (proClosedIso P s).symm ≪≫
  (towerCandidateComparison P.Coefficient c
    (HasCompactification.compactification f)).app
      ((originCompactSupport P.Coefficient s).obj (originUnit P B)) ≪≫
  (originCompositionAmbient P.Coefficient s f).app (originUnit P B) ≪≫
  (ProEtale.rightDerivedLowerShriekCongr (ModuleCat.{u + 1} P.Coefficient) hs).app _ ≪≫
  (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) B).ι.mapIso
    ((originCompactSupportId P.Coefficient B).app (originUnit P B)) ≪≫
  constantComparison P B

/-- The specified inverse-direction beta, including the D+ inclusion comparison.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def compactComparison {X B : Scheme.{u}} {f : X ⟶ B} (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} P.Coefficient) c).obj M).obj ≅
    (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        X).mapDerivedCategory.obj M.obj) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} P.Coefficient) c).app M) ≪≫
  ((compactSupportSiteComparison P.Coefficient c).app M).symm

/-- The specified psi = F^p(theta) beta_M; its type retains the actual isomorphism.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def targetComparison {X B : Scheme.{u}} {f : X ⟶ B} (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (theta : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        X).mapDerivedCategory.obj M.obj ≅ K.obj) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} P.Coefficient) c).obj M).obj ≅
    (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj K.obj :=
  compactComparison P c M ≪≫
    (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).mapIso theta

/-- The actual etale representative tau_e, without any invertibility assumption.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def etaleTau {B X : Scheme.{u}} (f : X ⟶ B) [QuasiCompact f]
    (c : Compactification f) (s : B ⟶ X) [IsClosedImmersion s] (hs : s ≫ f = 𝟙 B)
    {M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (ce : etaleSource P s ⟶ M) :
    etaleUnit P B ⟶ (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} P.Coefficient) c).obj M :=
  (etaleSigma P f c s hs).inv ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} P.Coefficient) c).map ce

/-- The actual pro-etale tau_p, with its identity-normalized source identification.
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def proTau {B X : Scheme.{u}} (f : X ⟶ B) [QuasiCompact f]
    (c : Compactification f) (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι] (hs : s ≫ f = 𝟙 B)
    {K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
    (cp : (proSource P s).obj ⟶ K.obj) :
    (proUnit P B).obj ⟶ (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj K.obj :=
  (proSigma P f c s hs).inv ≫
    (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).map cp

/-- The retained constant source witness is exactly (A_B^e, chi_B).
Source: blueprint Step 1 (blueprint: lem-pur-closed-section-compact-origin). -/
def sourceWitness (B : Scheme.{u}) :
    Scheme.FixedEtaleOriginWitness B P.Coefficient (proUnit P B) where
  complex := etaleUnit P B
  iso := constantComparison P B

end AlgebraicGeometry.ClosedSectionCompactOrigin
