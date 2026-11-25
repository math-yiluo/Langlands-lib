/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.GeoCartierCycleClassDefs

/-!
# The cycle class of an effective Cartier divisor

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier,
statement and proof paragraphs 1--6; Stacks Project, Tag 03PL
(blueprint: def-sfb-geo-cartier-interface).

We use the fixed-scalar sheaf presentation of ordinary pro-etale modules, canonically
realized by `finiteCoefficientRealization` over the coefficient ring sheaf of
`definition-small-pro-etale-site--1`. `Ext.homEquiv` identifies every degree-two Ext class
below with the displayed morphism from the degree-zero supported constant object to
its finite Tate line shifted by two. No condensed or completed coefficient category occurs.
The auxiliary definitions only spell out this class and its normalization diagrams.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A simultaneous family allows coefficient, exponent and geometric compatibility
between its actual members. Invertibility of ℓ^r equals invertibility of ℓ for r > 0.
Source: blueprint lemma-cycle-class-cartier-divisor, statement (blueprint:
def-sfb-geo-cartier-interface). -/
def GeoCartierClassFamily (ℓ : ℕ) : Type (u + 2) :=
  ∀ (r : ℕ) (_hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
    GeoCartierClass A (ℓ ^ r) hA i

/-- The inverse-image commutation isomorphism for the specified square.
Source: blueprint lemma-cycle-class-cartier-divisor, opening comparison and paragraph 6
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierPullbackSquare (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    upperStar (ModuleCat.{u + 1} A) g ⋙ upperStar (ModuleCat.{u + 1} A) i' ≅
      upperStar (ModuleCat.{u + 1} A) i ⋙ upperStar (ModuleCat.{u + 1} A) gD :=
  (upperStarComp (ModuleCat.{u + 1} A) i' g).symm ≪≫
    eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) sq.w.symm) ≪≫
    upperStarComp (ModuleCat.{u + 1} A) gD i

/-- Canonical pro-etale closed exchange, as the adjoint of inverse-image commutation
followed by the counit and the pullback of constants. This formula works for arbitrary
base morphisms; no weakly-etale or flatness restriction is imposed.
Source: blueprint lemma-cycle-class-cartier-divisor, proof paragraph 6
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierExchange (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar (ModuleCat.{u + 1} A) g).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (geoCartierConstant A D') :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').homEquiv _ _
    ((geoCartierPullbackSquare A i i' g gD sq).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) gD).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
            (geoCartierConstant A D)) ≫
        Scheme.proEtaleConstantInverseImageMap gD (ModuleCat.{u + 1} A) (ModuleCat.of A A))

/-- Pull back the finite Tate line through the canonical comparison square and the
existing roots-normalized etale transport.
Source: blueprint lemma-cycle-class-cartier-divisor, base-change clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {Z Z' : Scheme.{u}} (g : Z' ⟶ Z) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (upperStar (ModuleCat.{u + 1} A) g).obj (geoCartierLine A N hA Z) ≅
      geoCartierLine A N hA Z' :=
  (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).app
      (Scheme.finiteEtaleTateLine Z N A hA) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z').mapIso (t.line g hZ)

/-- The Chern equation is the actual Kummer boundary of the dual ideal line, expressed
in module Ext and then pulled back by ν. The integral generator fixes the usual
cohomological normalization; it does not supply an arbitrary Chern class.
Source: blueprint lemma-cycle-class-cartier-divisor, statement and proof paragraph 5
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierChernEquation (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z)
    (hI : i.ker.IsInvertible) (hZ : IsUnit (N : Γ(Z, ⊤)))
    (c : GeoCartierClass A N hA i) : Prop :=
  ∃ c₁ : Ext (Etale.ordinaryFiniteConstant A Z) (Scheme.finiteEtaleTateLine Z N A hA) 2,
    (Ext.mk₀ (Etale.ordinaryFiniteIntegralGenerator A Z)).comp
        (c₁.mapExactFunctor (Etale.RawModuleScalarComparison.forget A Z)) (zero_add 2) =
      Etale.supportedKummerChern A N hA i hI hZ ∧
    (Ext.mk₀ (((comparisonUpperStarConstantSheafIso A Z).app (ModuleCat.of A A)).hom ≫
      Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A) (ModuleCat.of A A))).comp
        c (zero_add 2) = c₁.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)

/-- Derived extension at a specified sheaf map is characterized by its Hom universal
property against every unbounded complex. This is a property of the given coefficient
unit, not a choice of a replacement scalar-extension functor.
Source: Stacks 07A6; blueprint lemma-cycle-class-cartier-divisor, coefficient clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (Z : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G) : Prop :=
  Sheaf.IsDerivedBaseChange
    ((DerivedCategory.singleFunctor _ 0).map η ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategorySingleFunctor
        0).inv.app G)

/-- Coefficient compatibility with the canonical supported-constant and Tate-line
units. Normalization is on constants and on pure root tensors through the comparison
adjunction unit. These generate after sheafification, so the comparisons are fixed.
Source: blueprint lemma-cycle-class-cartier-divisor, coefficient clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierScalarCompatibility {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z)
    (cR : GeoCartierClass R N hR i) (cS : GeoCartierClass S N hS i) : Prop :=
  ∃ (η : geoCartierConstant R D ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant S D))
    (θ : geoCartierLine R N hR Z ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj (geoCartierLine S N hS Z)),
    (∀ (W : D.ProEtᵒᵖ) (a : R),
      η.hom.app W ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of S S))).app W (φ a)) ∧
    (∀ (W : Z.Etaleᵒᵖ) (a : R) (z : (Z.rootsOfUnitySheaf N).obj.obj W),
      θ.hom.app ((Scheme.toProEt Z).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
          (Scheme.finiteEtaleTateLine Z N R hR)).hom.app W
            (Scheme.finiteEtaleTateOneGenerator R N Z hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).unit.app
        (Scheme.finiteEtaleTateLine Z N S hS)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator S N Z hS W (φ a) z)) ∧
    GeoCartierScalarUnit φ Z
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    GeoCartierScalarUnit φ Z (geoCartierLine R N hR Z) (geoCartierLine S N hS Z) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ))
        (zero_add 2) = cR.comp (Ext.mk₀ θ) (add_zero 2)

/-- Cartier-preserving pullback of a simultaneous class family, using the counit mate
for the source and the roots-normalized finite Tate-line comparison for the target.
Source: blueprint lemma-cycle-class-cartier-divisor, final clause (blueprint:
def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierBaseChange (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r : ℕ) (hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0),
    ∃ t : Etale.OrdinaryFiniteTwistTransport A (ℓ ^ r) hA,
      ∀ {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
        [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (gD : D' ⟶ D)
        (sq : IsPullback gD i' i g) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
        (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ r : ℕ) : Γ(Z', ⊤))),
        IsIso (geoCartierExchange A i i' g gD sq.toCommSq) ∧
        (Ext.mk₀ (geoCartierExchange A i i' g gD sq.toCommSq)).comp
            (c r hr A hA i' hI' hZ') (zero_add 2) =
          ((c r hr A hA i hI hZ).mapExactFunctor (upperStar (ModuleCat.{u + 1} A) g)).comp
            (Ext.mk₀ (geoCartierLinePullback A (ℓ ^ r) hA t g hZ).hom) (add_zero 2)

/-- Independence of the killing exponent under the actual roots projection. The map
on roots is pinned by its inclusion into G_m, and the line map by its pure tensors.
Source: blueprint lemma-cycle-class-cartier-divisor, exponent sentence
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierExponentIndependence (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (_hrs : r ≤ s)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) (hA' : ((ℓ ^ s : ℕ) : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ s : ℕ) : Γ(Z, ⊤))),
    ∃ (q : Z.rootsOfUnitySheaf (ℓ ^ s) ⟶ Z.rootsOfUnitySheaf (ℓ ^ r))
      (e : Scheme.finiteEtaleTateLine Z (ℓ ^ s) A hA' ≅
        Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA),
      q ≫ kernel.ι ((ℓ ^ r) • 𝟙 Z.gmSheaf) =
        (ℓ ^ s / ℓ ^ r) • kernel.ι ((ℓ ^ s) • 𝟙 Z.gmSheaf) ∧
      (∀ (W : Z.Etaleᵒᵖ) (a : A) (z : (Z.rootsOfUnitySheaf (ℓ ^ s)).obj.obj W),
        e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A (ℓ ^ s) Z hA' W a z) =
          Scheme.finiteEtaleTateOneGenerator A (ℓ ^ r) Z hA W a (q.hom.app W z)) ∧
      (c s hs A hA' i hI hZ').comp
          (Ext.mk₀ ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).map e.hom)) (add_zero 2) =
        c r hr A hA i hI hZ

end AlgebraicGeometry.ProEtale
