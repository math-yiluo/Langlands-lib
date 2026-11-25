/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
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
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange

/-!
# Construction of the affine-space counit trace

Source: blueprint sec-smooth-purity/sk-prop-an, Steps 5(b) and 6, detailed lemma
lemma-integral-linear-character--1 (blueprint: def-amb-affine-trace-construction).

The coordinate model is `affineTraceTower S d`. Its unbounded left functor and right
functor are ordered composites of the affine-line functors; the zero-dimensional
adjunction is literally the identity. In the right functor, each coordinate contributes
one ordinary finite Tate line and a shift by two. This is the coordinate-tower expression
for p* K(d)[2d], with the canonical tensor, shift and inverse-image identifications.
The bounded-below comparison below uses the existing coherent compact-support composition
isomorphisms. Neither the counit nor its base-change map is chosen independently.

## Main definitions and statement

- `affineTraceAdjunction`: the specified ordered open/projective composite.
- `affineTraceCompactSupportComparison`: the canonical comparison on D+.
- `affineTraceCounit`: its actual counit at the constant coefficient complex.
- `affineTraceExchange`: the coordinatewise pasted compact-support exchange.
- `exists_affineSpaceTopTrace`: invertibility and arbitrary Noetherian base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Exact derived extension by zero for the standard chart, recorded once.
Source: the exact derived open extension
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceOpenLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) ⥤
      DerivedCategoryModule A (ProjectiveLine S) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.affineChart S)).mapDerivedCategory

/-- One affine-line left functor, on its specified standard compactification.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-construction). -/
abbrev affineTraceLineLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) ⥤ DerivedCategoryModule A S :=
  affineTraceOpenLeft A S ⋙ ordinaryFinitePushforward A (ProjectiveLine S ↘ S)

/-- The right functor obtained by restricting the normalized projective-line right
functor to the standard affine chart. Source: blueprint proposition-purity-vector-bundles, Step 5(b)
(blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLineRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    DerivedCategoryModule A S ⥤ DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S) :=
  ordinaryFiniteP1Right A N hA S ⋙ ordinaryFinitePullback A (ProjectiveLine.affineChart S)

/-- The derived open adjunction with its ordinary inverse-image functor recorded once.
Source: the exact derived open adjunction
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceOpenAdjunction (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineTraceOpenLeft A S ⊣ ordinaryFinitePullback A (ProjectiveLine.affineChart S) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine.affineChart S)).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart S)).symm

attribute [irreducible] affineTraceOpenAdjunction

/-- Ordered left composites for a family of categories.
Source: Mathlib adjunction composition (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLeftTower {C : ℕ → Type*} [∀ d, Category (C d)]
    (L : ∀ d, C (d + 1) ⥤ C d) : (d : ℕ) → C d ⥤ C 0 :=
  Nat.rec (motive := fun d ↦ C d ⥤ C 0) (𝟭 _) (fun d F ↦ L d ⋙ F)

/-- Ordered right composites for a family of categories.
Source: Mathlib adjunction composition (blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceRightTower {C : ℕ → Type*} [∀ d, Category (C d)]
    (R : ∀ d, C d ⥤ C (d + 1)) : (d : ℕ) → C 0 ⥤ C d :=
  Nat.rec (motive := fun d ↦ C 0 ⥤ C d) (𝟭 _) (fun d G ↦ G ⋙ R d)

/-- The ordered unbounded left functor of the coordinate tower.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
abbrev affineTraceLeft (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A (affineTraceTower S d) ⥤ DerivedCategoryModule A S :=
  affineTraceLeftTower (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower S d))

/-- The ordered right functor: p* K(d)[2d] written as the iterated shifted-line twists.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
abbrev affineTraceRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A S ⥤ DerivedCategoryModule A (affineTraceTower S d) :=
  affineTraceRightTower (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (fun d ↦ affineTraceLineRight A N hA (affineTraceTower S d))

/-- Composite adjunction with its counit written componentwise.
This is Mathlib's composite, with the same unit and counit; the explicit components
avoid expanding the associator implementation in coordinate inductions.
Source: blueprint affine-space top trace, step 7
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceComposeAdjunction
    {C : Type*} {E : Type*} {F : Type*}
    [Category C] [Category E] [Category F]
    {L : C ⥤ E} {R : E ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') : L ⋙ L' ⊣ R' ⋙ R := by
  let c : (R' ⋙ R) ⋙ (L ⋙ L') ⟶ 𝟭 F :=
    { app := fun X ↦ L'.map (a.counit.app (R'.obj X)) ≫ b.counit.app X
      naturality := fun X Y f ↦ by
        have ha := a.counit.naturality (R'.map f)
        have hb := b.counit.naturality f
        simp only [Functor.comp_map, Functor.id_map] at ha hb ⊢
        rw [← Category.assoc, ← L'.map_comp, ha, L'.map_comp,
          Category.assoc, hb, ← Category.assoc] }
  have h : c = (a.comp b).counit := by
    ext X
    exact (Adjunction.comp_counit_app a b X).symm
  exact
    { unit := (a.comp b).unit
      counit := c
      left_triangle_components := fun X ↦ by
        rw [h]
        exact (a.comp b).left_triangle_components X
      right_triangle_components := fun X ↦ by
        rw [h]
        exact (a.comp b).right_triangle_components X }

/-- Component formula for the explicit composite.
Source: Mathlib `Adjunction.comp_counit_app`
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceComposeAdjunction_counit
    {C : Type*} {E : Type*} {F : Type*}
    [Category C] [Category E] [Category F]
    {L : C ⥤ E} {R : E ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') (X : F) :
    (affineTraceComposeAdjunction a b).counit.app X =
      L'.map (a.counit.app (R'.obj X)) ≫ b.counit.app X := by
  rfl

/-- The explicit-component presentation is the original composite adjunction.
Source: Mathlib `Adjunction.ext` and `Adjunction.comp_counit_app`
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceComposeAdjunction_eq
    {C : Type*} {E : Type*} {F : Type*}
    [Category C] [Category E] [Category F]
    {L : C ⥤ E} {R : E ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') :
    affineTraceComposeAdjunction a b = a.comp b := by
  apply Adjunction.ext
  rfl

/-- Compose the actual open adjunction with the actual normalized projective adjunction.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-construction). -/
abbrev affineTraceLineAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (D : OrdinaryFiniteP1Datum A N hA t S hS) :
    affineTraceLineLeft A S ⊣ affineTraceLineRight A N hA S :=
  affineTraceComposeAdjunction (affineTraceOpenAdjunction A S) D.adjunction

/-- The line counit in open/proper components.
Source: the explicit composite counit
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceLineAdjunction_counit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (D : OrdinaryFiniteP1Datum A N hA t S hS) (K : DerivedCategoryModule A S) :
    (affineTraceLineAdjunction A N hA t S hS D).counit.app K =
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
        ((affineTraceOpenAdjunction A S).counit.app
          ((ordinaryFiniteP1Right A N hA S).obj K)) ≫ D.adjunction.counit.app K := by
  unfold affineTraceLineAdjunction
  exact affineTraceComposeAdjunction_counit _ _ _

/-- Ordered composite adjunctions in a family of abstract categories.
Source: Mathlib adjunction composition (blueprint: def-amb-affine-trace-construction). -/
def affineTraceAdjunctionTower {C : ℕ → Type*} [∀ d, Category (C d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {R : ∀ d, C d ⥤ C (d + 1)}
    (a : ∀ d, L d ⊣ R d) : (d : ℕ) →
      affineTraceLeftTower L d ⊣ affineTraceRightTower R d :=
  Nat.rec (motive := fun d ↦ affineTraceLeftTower L d ⊣ affineTraceRightTower R d)
    Adjunction.id (fun d b ↦ affineTraceComposeAdjunction (a d) b)

/-- Successor counit formula, checked before specializing the category instances.
Source: Mathlib `Adjunction.comp_counit_app`
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceAdjunctionTower_counit_succ {C : ℕ → Type*} [∀ d, Category (C d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {R : ∀ d, C d ⥤ C (d + 1)}
    (a : ∀ d, L d ⊣ R d) (d : ℕ) (K : C 0) :
    (affineTraceAdjunctionTower a (d + 1)).counit.app K =
      (affineTraceLeftTower L d).map
        ((a d).counit.app ((affineTraceRightTower R d).obj K)) ≫
      (affineTraceAdjunctionTower a d).counit.app K := by
  rfl

/-- Invertible coordinate counits give invertible composite counits.
Source: blueprint affine-space trace, step 7
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceAdjunctionTower_counit_isIso {C : ℕ → Type*} [∀ d, Category (C d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {R : ∀ d, C d ⥤ C (d + 1)}
    (a : ∀ d, L d ⊣ R d) (ha : ∀ d K, IsIso ((a d).counit.app K))
    (d : ℕ) (K : C 0) : IsIso ((affineTraceAdjunctionTower a d).counit.app K) := by
  induction d with
  | zero => change IsIso (𝟙 K); infer_instance
  | succ d ih =>
    rw [affineTraceAdjunctionTower_counit_succ]
    have := ha d ((affineTraceRightTower R d).obj K)
    infer_instance

/-- The literal composite adjunction, with the literal identity adjunction in dimension zero.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceAdjunction (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → affineTraceLeft A S d ⊣ affineTraceRight A N hA S d
  := affineTraceAdjunctionTower
    (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (fun d ↦ affineTraceLineAdjunction A N hA t (affineTraceTower S d)
      (affineTraceInvertible N S hS d)
      (@D (affineTraceTower S d) (affineTraceNoetherian S d)
        (affineTraceInvertible N S hS d)))

attribute [irreducible] affineTraceAdjunction

/-- The actual trace, the counit at the constant coefficient complex. Its source is
F_d applied to the coordinate-tower model of A(d)[2d].
Source: blueprint proposition-purity-vector-bundles, Steps 5(b), 6 (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceCounit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :=
  (affineTraceAdjunction A N hA t D S hS d).counit.app (ordinaryFiniteUnit A S)

/-- The bounded-below version of the same ordered left functor.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceLeftPlus (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategory.Plus
        (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
  | 0 => 𝟭 _
  | d + 1 => rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d)) ⋙ affineTraceLeftPlus A S d

/-- The canonical coherent comparison of the ordered tower with Rp_d! on D+.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceCompactSupportComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] : (d : ℕ) →
    affineTraceLeftPlus A S d ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (affineTraceProjection S d)
  | 0 => (rightDerivedLowerShriekPlusId A S).symm
  | d + 1 =>
    letI := affineTraceNoetherian S d
    let e₁ := rightDerivedLowerShriekOfCompactificationPlusIso A
      (f := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceLineCompactification (affineTraceTower S d))
      (HasCompactification.compactification
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d))
    let e₂ := affineTraceCompactSupportComparison A S d
    let e₃ := rightDerivedLowerShriekPlusCompIso A
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d)
    Functor.isoWhiskerRight e₁ (affineTraceLeftPlus A S d) ≪≫
      Functor.isoWhiskerLeft
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)) e₂ ≪≫ e₃

/-- The restriction of the unbounded tower to D+ is its bounded-below tower.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
def affineTracePlusCompatibility (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (d : ℕ) → affineTraceLeftPlus A S d ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ affineTraceLeft A S d
  | 0 => Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  | d + 1 =>
    let L := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let F := affineTraceLeftPlus A S d
    let l := affineTraceLineLeft A (affineTraceTower S d)
    let f := affineTraceLeft A S d
    let e := rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower S d))
    let r := affineTracePlusCompatibility A S d
    Functor.associator L F DerivedCategory.Plus.ι ≪≫
      Functor.isoWhiskerLeft L r ≪≫
      (Functor.associator L DerivedCategory.Plus.ι f).symm ≪≫
      Functor.isoWhiskerRight e f ≪≫ Functor.associator DerivedCategory.Plus.ι l f

/-- The natural transformation underlying the standard affine-line exchange.
It is the proper exchange followed by the open exchange and compactification comparison.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceLineExchangeTransformation (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) :
    affineTraceLineLeft A S ⋙ ordinaryFinitePullback A f ⟶
      ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f) ⋙
        affineTraceLineLeft A S' :=
  let e₁ := rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)
    (affineTraceLineCompactification S)
  let e₂ := rightDerivedLowerShriekOfCompactificationIso A
    ((affineTraceLineCompactification S).ofIsPullback
      (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f))
    (affineTraceLineCompactification S')
  e₁ ≫ Functor.whiskerLeft _ e₂.hom

attribute [irreducible] affineTraceLineExchangeTransformation

/-- Canonical proper exchange followed by open exchange and the coherent comparison
back to the standard compactification on the changed base.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceLineExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    (ordinaryFinitePullback A f).obj ((affineTraceLineLeft A S).obj M) ⟶
      (affineTraceLineLeft A S').obj
        ((ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj M) :=
  (affineTraceLineExchangeTransformation A f).app M

attribute [irreducible] affineTraceLineExchange

/-- Packaging the line exchange preserves its original component map.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-construction). -/
theorem affineTraceLineExchange_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S)) :
    affineTraceLineExchange A f M =
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
        (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f)
        (affineTraceLineCompactification S)).app M ≫
      (rightDerivedLowerShriekOfCompactificationIso A
        ((affineTraceLineCompactification S).ofIsPullback
          (AffineSpace.isPullback_map (n := PUnit.{u + 1}) f))
        (affineTraceLineCompactification S')).hom.app _ := by
  unfold affineTraceLineExchange affineTraceLineExchangeTransformation
  rfl

/-- Paste exchange squares along ordered towers of abstract categories.
Source: blueprint affine-space trace, step 9
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceExchangeTower {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (L : ∀ d, C (d + 1) ⥤ C d) (L' : ∀ d, C' (d + 1) ⥤ C' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d) :
    (d : ℕ) → affineTraceLeftTower L d ⋙ B 0 ⟶ B d ⋙ affineTraceLeftTower L' d
  | 0 => (B 0).leftUnitor.hom ≫ (B 0).rightUnitor.inv
  | d + 1 =>
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L d) (affineTraceExchangeTower L L' B e d) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (e d) (affineTraceLeftTower L' d) ≫
      (Functor.associator _ _ _).hom

/-- Component formula for a pasted exchange at dimension zero.
Source: identity natural transformation (blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceExchangeTower_zero {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (L : ∀ d, C (d + 1) ⥤ C d) (L' : ∀ d, C' (d + 1) ⥤ C' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (M : C 0) : (affineTraceExchangeTower L L' B e 0).app M = 𝟙 _ := by
  simp [affineTraceExchangeTower]

/-- Component formula for a pasted successor exchange.
Source: composition of natural transformations
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceExchangeTower_succ {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (L : ∀ d, C (d + 1) ⥤ C d) (L' : ∀ d, C' (d + 1) ⥤ C' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (d : ℕ) (M : C (d + 1)) :
    (affineTraceExchangeTower L L' B e (d + 1)).app M =
      (affineTraceExchangeTower L L' B e d).app ((L d).obj M) ≫
        (affineTraceLeftTower L' d).map ((e d).app M) := by
  simp [affineTraceExchangeTower]

/-- The canonical exchange of the ordered coordinate tower, obtained by pasting the
proper/open exchanges of its coordinate steps. Source: blueprint proposition-purity-vector-bundles,
Step 6 (blueprint: def-amb-affine-trace-construction). -/
def affineTraceExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) (d : ℕ)
    (M : DerivedCategoryModule A (affineTraceTower S d)) :
    (ordinaryFinitePullback A f).obj ((affineTraceLeft A S d).obj M) ⟶
      (affineTraceLeft A S' d).obj
        ((ordinaryFinitePullback A (affineTraceMap f d)).obj M) :=
  (affineTraceExchangeTower
    (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (C' := fun d ↦ DerivedCategoryModule A (affineTraceTower S' d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower S d))
    (fun d ↦ affineTraceLineLeft A (affineTraceTower S' d))
    (fun d ↦ ordinaryFinitePullback A (affineTraceMap f d))
    (fun d ↦ affineTraceLineExchangeTransformation A (affineTraceMap f d)) d).app M

/-- The inverse-image comparison around the standard affine-chart square.
Source: blueprint proposition-purity-vector-bundles, Step 5(b) (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceOpenPullbackSquare (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) :
    ordinaryFinitePullback A (ProjectiveLine.affineChart S) ⋙
        ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f) ≅
      ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) ⋙
        ordinaryFinitePullback A (ProjectiveLine.affineChart S') :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map PUnit.{u + 1} f) (ProjectiveLine.affineChart S)).symm ≪≫
  eqToIso (congrArg (ordinaryFinitePullback A) (affineTraceChart_isPullback f).w) ≪≫
  leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart S')
    (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)

/-- A square comparison followed by inverse image of an object comparison.
Source: composition of natural and object isomorphisms
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceRightSquareIso
    {D E D' E' : Type*} [Category D] [Category E] [Category D'] [Category E']
    {U : D ⥤ E} {B2 : E ⥤ E'} {B1 : D ⥤ D'} {U' : D' ⥤ E'}
    (s : U ⋙ B2 ≅ B1 ⋙ U') (M : D) {M' : D'} (c : B1.obj M ≅ M') :
    B2.obj (U.obj M) ≅ U'.obj M' where
  hom := s.hom.app M ≫ U'.map c.hom
  inv := U'.map c.inv ≫ s.inv.app M
  hom_inv_id := by simp [Category.assoc]
  inv_hom_id := by simp [Category.assoc]

/-- The explicit square comparison is the usual composite isomorphism.
Source: functoriality of isomorphisms
(blueprint: def-amb-affine-trace-construction). -/
theorem affineTraceRightSquareIso_eq
    {D E D' E' : Type*} [Category D] [Category E] [Category D'] [Category E']
    {U : D ⥤ E} {B2 : E ⥤ E'} {B1 : D ⥤ D'} {U' : D' ⥤ E'}
    (s : U ⋙ B2 ≅ B1 ⋙ U') (M : D) {M' : D'} (c : B1.obj M ≅ M') :
    affineTraceRightSquareIso s M c = s.app M ≪≫ U'.mapIso c := by
  apply Iso.ext
  rfl

/-- The same square comparison with the composite right functors in its interface.
Keeping the composite functors avoids comparing inverse-image objects with different
source categories after specialization to schemes.
Source: composition of the two right functors
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceCompositeRightSquareIso
    {C D E C' D' E' : Type*} [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {R : C ⥤ D} {R' : C' ⥤ D'} {B : C ⥤ C'}
    {U : D ⥤ E} {B2 : E ⥤ E'} {B1 : D ⥤ D'} {U' : D' ⥤ E'}
    (s : U ⋙ B2 ≅ B1 ⋙ U') (K : C)
    (c : B1.obj (R.obj K) ≅ R'.obj (B.obj K)) :
    B2.obj ((R ⋙ U).obj K) ≅ (R' ⋙ U').obj (B.obj K) :=
  affineTraceRightSquareIso s (R.obj K) c

/-- Canonical pullback of the one-coordinate right functor, with the normalized
roots-of-unity Tate comparison. Source: blueprint proposition-purity-vector-bundles, Step 5(b)
(blueprint: def-amb-affine-trace-construction). -/
abbrev affineTraceLineRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} f)).obj
        ((affineTraceLineRight A N hA S).obj K) ≅
      (affineTraceLineRight A N hA S').obj ((ordinaryFinitePullback A f).obj K) :=
  affineTraceCompositeRightSquareIso
    (R := ordinaryFiniteP1Right A N hA S) (R' := ordinaryFiniteP1Right A N hA S')
    (B := ordinaryFinitePullback A f) (affineTraceOpenPullbackSquare A f) K
    (ordinaryFiniteP1RightBaseChange A N hA t f hP K)

/-- One pasting step for the canonical right-functor base-change comparison.
The last argument is the preceding coordinate comparison; no map is chosen here.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceRightBaseChangeStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (e : (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} (affineTraceMap f d))).obj
        ((affineTraceLineRight A N hA (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S d).obj K)) ≅
      (affineTraceLineRight A N hA (affineTraceTower S' d)).obj
        ((affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K)) :=
  affineTraceLineRightBaseChange A N hA t (affineTraceMap f d)
    (affineTraceProjectiveInvertible N (affineTraceTower S d)
      (affineTraceInvertible N S hS d)) ((affineTraceRight A N hA S d).obj K) ≪≫
    (affineTraceLineRight A N hA (affineTraceTower S' d)).mapIso e

/-- Paste right-functor comparisons along an ordered tower.
Source: blueprint affine-space trace, step 9
(blueprint: def-amb-affine-trace-construction). -/
def affineTraceRightExchangeTower {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (R : ∀ d, C d ⥤ C (d + 1)) (R' : ∀ d, C' d ⥤ C' (d + 1))
    (B : ∀ d, C d ⥤ C' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K)) :
    (d : ℕ) → (K : C 0) →
      (B d).obj ((affineTraceRightTower R d).obj K) ≅
        (affineTraceRightTower R' d).obj ((B 0).obj K)
  | 0, _ => Iso.refl _
  | d + 1, K => r d _ ≪≫ (R' d).mapIso (affineTraceRightExchangeTower R R' B r d K)

/-- The canonical right-functor base-change comparison, pasted coordinatewise.
Source: blueprint proposition-purity-vector-bundles, Step 6 (blueprint:
def-amb-affine-trace-construction). -/
def affineTraceRightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (affineTraceMap f d)).obj
        ((affineTraceRight A N hA S d).obj K) ≅
      (affineTraceRight A N hA S' d).obj ((ordinaryFinitePullback A f).obj K) :=
  affineTraceRightExchangeTower
    (C := fun d ↦ DerivedCategoryModule A (affineTraceTower S d))
    (C' := fun d ↦ DerivedCategoryModule A (affineTraceTower S' d))
    (fun d ↦ affineTraceLineRight A N hA (affineTraceTower S d))
    (fun d ↦ affineTraceLineRight A N hA (affineTraceTower S' d))
    (fun d ↦ ordinaryFinitePullback A (affineTraceMap f d))
    (fun d K ↦ affineTraceLineRightBaseChange A N hA t (affineTraceMap f d)
      (affineTraceProjectiveInvertible N (affineTraceTower S d)
        (affineTraceInvertible N S hS d)) K) d K

end AlgebraicGeometry.Etale
