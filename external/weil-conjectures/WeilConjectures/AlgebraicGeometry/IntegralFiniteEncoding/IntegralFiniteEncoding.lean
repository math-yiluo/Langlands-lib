/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.LocalSite
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.Topology.Constructible
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Abelian.RightDerived
import all Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Sites.Precoverage
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import all WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import all WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.CategoryTheory.RightDerivedExactComposite
import all WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import all WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import all WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import all WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
public import WeilConjectures.AlgebraicGeometry.SfbCompletionRingComparison
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback

/-! # Finite internal coefficients on the coefficient-sized site

## References

* Stacks Tags 00YV and 03CY
* Stacks Tag 099Y
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralFiniteEncoding

instance smallProEtaleDownDense (X : Scheme.{u}) :
    (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
  change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsDenseSubsite
    (AsSmall.down.inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
  infer_instance

instance smallConstantDerived (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    HasDerivedCategory (CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) A)) :=
  HasDerivedCategory.standard _

instance smallFixedScalarsAdditive (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, u} X) A).Additive :=
  ⟨by intro M N f g; ext V m; rfl⟩

instance smallFixedScalarsIsEquivalence (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (coefficientModelFixedScalars
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) A).IsEquivalence :=
  AlgebraicGeometry.ProEtale.scalars_equivalence
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) A

def smallFixedScalarsEquivalence (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) A) ≌
    Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} A) :=
  (coefficientModelFixedScalars _ A).asEquivalence

def smallSiteSheafEquivalence (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ≌
      Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} A) :=
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  let : e.inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) :=
    smallProEtaleDownDense X
  e.sheafCongr (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} A)

/-- The normalized section-action encoding followed by the actual AsSmall equivalence
and inverse constant-scalar restriction. -/
def finiteEncodingFunctor (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A X) :
    FiniteDiscreteOrdinary.Internal A X ⥤
    CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1} A)) :=
  e.ordinary.functor ⋙ e.fixed.functor ⋙
    (smallSiteSheafEquivalence X (ULift.{u + 1} A)).functor ⋙
    (smallFixedScalarsEquivalence X (ULift.{u + 1} A)).inverse

instance finiteEncoding_equivalence (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A X) :
    (finiteEncodingFunctor A X e).IsEquivalence := by
  unfold finiteEncodingFunctor
  infer_instance

instance finiteEncoding_additive (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A X) :
    (finiteEncodingFunctor A X e).Additive := by
  let D := smallSiteSheafEquivalence X (ULift.{u + 1} A)
  let : D.functor.Additive := ⟨by intro M N f g; ext V m; rfl⟩
  let : (smallFixedScalarsEquivalence X (ULift.{u + 1} A)).functor.Additive :=
    inferInstanceAs (coefficientModelFixedScalars _ (ULift.{u + 1} A)).Additive
  dsimp only [finiteEncodingFunctor]
  infer_instance

/-- Exact derived encoding into constant-ring modules on the coefficient-sized site. -/
def finiteEncodingDerived (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A X) :=
  (finiteEncodingFunctor A X e).mapDerivedCategory

end AlgebraicGeometry.ProEtale.IntegralFiniteEncoding
