/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRingStrictFiniteExchange
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Basic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeLimitNormalization
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenScalarLimitSquare
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenStrictMateTranspose
import WeilConjectures.AlgebraicGeometry.CompletedOpenFiniteTranspose.CompletedOpenFiniteTransposeCoherence

/-!
# The actual completed open exchange and its strict constant-coefficient mate

Source: Stacks Project, Tag 03DI, explicit extension-by-zero unit transpose;
blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange and final limit.
(blueprint: lem-cbc-completed-open-strict-mate-identification).

The endpoint comparisons reuse the published scalar, strict quotient, and normalized
inverse-limit comparisons. The actual strict exchange is constructed before evaluation.
The endpoint constructions and their naturality properties from
CompleteProetaleStrictTowerRealization are used; its compact-support realization theorem
is not used in this module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint limit Functor.mapDerivedCategory Functor.rightDerivedFunctor

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
  (sq : OpenImmersionSquare v j' j g)

/-- The actual source Q, using reduction of j!K before strict derived pullback.
Source: blueprint finite open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateSource :=
  cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d ⋙
    completedTowerPullback g d

/-- The actual target Q', with strict pullback preceding strict open extension.
Source: blueprint finite open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateTarget :=
  completedReductionTower U d ⋙ completedTowerPullback v d ⋙
    cbcStrictOpen d j' inferInstance

/-- The specified actual strict exchange, transported by the canonical quotient/open
comparison. Both constituent isomorphisms are already defined before evaluation.
Source: Stacks 03DI and blueprint finite exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateOmega (K : d.derived U) :
    (cbcOpenMateSource d (j := j) (g := g)).obj K ≅
      (cbcOpenMateTarget d (j' := j') (v := v)).obj K :=
  (completedTowerPullback g d).mapIso (cbcRealizationReduction d j K) ≪≫
    (cbcReductionStrictExchange d sq).app K

/-- M is the scalar restriction of the entire strict reduction tower of K.
Source: Stacks 099M and blueprint finite reductions
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateM := completedReductionTower U d ⋙ exchangeTowerRes d U

/-- N = G_g J_j M, in the derived category of constant-A strict towers.
Source: blueprint strict open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateN :=
  cbcOpenMateM d (U := U) ⋙ ProEtale.StrictTower.J A j ⋙ ProEtale.StrictTower.G A g

/-- N' = J_j' G_v M, with the same strict constant-coefficient operations.
Source: blueprint strict open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateN' :=
  cbcOpenMateM d (U := U) ⋙ ProEtale.StrictTower.G A v ⋙ ProEtale.StrictTower.J A j'

/-- The canonical source comparison a: r(Q) is identified with G_g J_j M.
It uses the normalized actual-to-datum pullback comparison, the scalar/pullback
comparison, and the quotient/open comparison, in that order.
Source: Stacks 03DI, 099N and blueprint scalar comparisons
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateA (K : d.derived U) :
    (exchangeTowerRes d T').obj ((cbcOpenMateSource d (j := j) (g := g)).obj K) ≅
      (cbcOpenMateN d (j := j) (g := g)).obj K :=
  (exchangeTowerRes d T').mapIso
      ((cbcDatumTowerTransport d g).app
        ((completedReductionTower T d).obj
          ((cbcDerivedOpenShriek d j inferInstance).obj K))) ≪≫
    (exchangeResPull d g).app _ ≪≫
    (ProEtale.StrictTower.G A g).mapIso (cbcRealizationQuotientOpen d j K)

/-- The canonical target comparison b: r(Q') is identified with J_j' G_v M.
It first transports strict pullback, then commutes scalar restriction with open
extension, and finally uses the scalar/pullback comparison inside J_j'.
Source: Stacks 03DI, 099N and blueprint scalar comparisons
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateB (K : d.derived U) :
    (exchangeTowerRes d T').obj ((cbcOpenMateTarget d (j' := j') (v := v)).obj K) ≅
      (cbcOpenMateN' d (j' := j') (v := v)).obj K :=
  (exchangeTowerRes d T').mapIso
      ((cbcStrictOpen d j' inferInstance).mapIso
        ((cbcDatumTowerTransport d v).app ((completedReductionTower U d).obj K))) ≪≫
    (cbcRealizationTowerScalarOpen d j').app _ ≪≫
    (ProEtale.StrictTower.J A j').mapIso
      ((exchangeResPull d v).app ((completedReductionTower U d).obj K))

/-- The already specified constant-A strict open unit-mate, at M = r(K_bullet).
Source: Stacks 03DI, normalized strict open calculus
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateBeta (K : d.derived U) :
    (cbcOpenMateN d (j := j) (g := g)).obj K ≅
      (cbcOpenMateN' d (j' := j') (v := v)).obj K :=
  (ProEtale.StrictTower.beta A v j' j g sq.w
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).app
      ((cbcOpenMateM d (U := U)).obj K)

/-- Quasi-compactness of the base-changed open, supplied by the cartesian square.
Source: Stacks 01K5
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateQC [QuasiCompact j] : QuasiCompact j' :=
  MorphismProperty.of_isPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
    (inferInstance : QuasiCompact j)

/-- The completed source endpoint, including the specified scalar/limit comparison
and strict quotient/open identification. No endpoint isomorphism is freely chosen.
Source: Stacks 099M, 099N and blueprint ordered limit
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateCompletedA (K : d.derived U) :
    (cbcRealizationRes d T').mapDerivedCategory.obj
        ((d.completedPull g).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)) ≅
      (completedRlim T' (exchangeConstantRing T' A)).obj
        ((cbcOpenMateN d (j := j) (g := g)).obj K) :=
  cbcRealizationPullLimit d g ((cbcDerivedOpenShriek d j inferInstance).obj K) ≪≫
    (completedRlim T' (exchangeConstantRing T' A)).mapIso
      ((ProEtale.StrictTower.G A g).mapIso (cbcRealizationQuotientOpen d j K))

/-- The completed target endpoint, before applying the normalized constant-A
open/limit comparison. The coefficient and pullback comparisons retain their units.
Source: Stacks 03DI, 099N and blueprint ordered limit
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateCompletedB (K : d.derived U) :
    (cbcRealizationRes d T').mapDerivedCategory.obj
        ((cbcDerivedOpenShriek d j' inferInstance).obj ((d.completedPull v).obj K)) ≅
      (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory.obj
        ((completedRlim U' (exchangeConstantRing U' A)).obj
          ((ProEtale.StrictTower.G A v).obj ((cbcOpenMateM d (U := U)).obj K))) :=
  (cbcRealizationDerivedScalarOpen d j').app ((d.completedPull v).obj K) ≪≫
    (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory.mapIso
      (cbcRealizationPullLimit d v K)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem forward_of_inverse
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {Q Q' : C} {N N' : D} (w : Q ≅ Q') (b : F.obj Q' ≅ N')
    (a : F.obj Q ≅ N) (t : N ≅ N')
    (h : b.inv ≫ F.map w.inv ≫ a.hom = t.inv) :
    F.map w.hom ≫ b.hom = a.hom ≫ t.hom := by
  apply (cancel_epi (F.map w.inv)).1
  rw [← Category.assoc, ← F.map_comp, w.inv_hom_id, F.map_id, Category.id_comp]
  have hi : F.map w.inv ≫ a.hom = b.hom ≫ t.inv := by
    apply (cancel_epi b.inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  rw [← Category.assoc, hi, Category.assoc, t.inv_hom_id, Category.comp_id]

attribute [local irreducible] ProEtale.StrictTower.beta ProEtale.StrictTower.jAdj
  ProEtale.StrictTower.squareG CompletedOpenFiniteTranspose.constantSquare

end AlgebraicGeometry.Scheme
