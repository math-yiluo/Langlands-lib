/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Rational.RationalFibrePathConstruction
public import Mathlib.CategoryTheory.Localization.Construction
public import WeilConjectures.AlgebraicGeometry.Rational.RationalFibrePathScalarSquare
public import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientFiberComparisons
public import WeilConjectures.CategoryTheory.Pseudofunctor.NormalizedFibreComparisons
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.TateTwist.ProEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RepresentationTheory.Coinvariants

/-! # Geometric curve compact-support cohomology

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-fourier-transform/sec-perverse-t-exactness-of-the-fourier-transform/sk-p-dl-a1-perverse/`
`sk-p-dl-a1-perverse.proof.md`, right exactness and localization/coinvariant sentences
(blueprint: lem-per-geometric-curve-compact-cohomology).
The declaration below records the complete geometric statement; its proof is postponed to a
later stage.  Compact cohomology is the project’s actual condensed lower-shriek construction,
and the finite-support hypothesis is written as vanishing after restriction to the complement of
a finite set of closed points.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedCurve

/-- The finite-subextension-valued condensed ring `Q = Qbar_ℓ`; an abbreviation of
`Profinite.padicAlgClRingObj`, introducing no new coefficient ring.
Source: `prose-02-50`, as cited in the statement of the node
(blueprint: lem-per-geometric-curve-compact-cohomology). -/
abbrev CurveCoeff (ℓ : ℕ) [Fact ℓ.Prime] := Profinite.padicAlgClRingObj ℓ

/-- Modules over `Q_X = p_X^* Q` on the small pro-étale site; the same category as
`CondensedLisseMonodromy.Modules`, introducing no new notion.
Source: `prose-02-51`, as cited in the statement of the node
(blueprint: lem-per-geometric-curve-compact-cohomology). -/
abbrev CurveModules (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (CurveCoeff ℓ) X)

end AlgebraicGeometry.ProEtale.CondensedCurve
