/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf

/-!
# Integral open direct image preserves constructibility

The residue comparison is specified by its adjunction equation, rather than by an
unconstrained isomorphism of objects. The coefficient-change pullback square used in that
equation is defined for the nonflat residue quotient. All derived categories below are
ordinary derived categories of internal modules over the continuous condensed coefficients.

## References

* Stacks Tags 099L, 09A6, 09C1
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralOpenDirectImage

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- The canonical pullback/reduction transformation, obtained by transposing the inverse
of the exact restriction-of-scalars pullback square along the two derived scalar
adjunctions. No flatness of O_E -> F_E is assumed. -/
def reductionPullbackMap :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙
        AdicCompletion.derivedReduction l E U 0 ⟶
      AdicCompletion.derivedReduction l E X 0 ⋙
        (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory :=
  ((mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X 0))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U 0))).symm
      (TwoSquare.mk _ _ _ _
        (CondensedRing.derivedComapUpperStarIso (DerivedNakayama.reductionRing l E 1) j).inv)
    )

private theorem unique_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (R : C ⥤ C') (S : D ⥤ D')
    (χ : F ⋙ S ⟶ R ⋙ F') [IsIso χ] (K : D)
    (hc : IsIso ((adj'.homEquiv _ _)
      (inv (χ.app (G.obj K)) ≫ S.map (adj.counit.app K)))) :
    ∃! c : R.obj (G.obj K) ⟶ G'.obj (S.obj K),
      IsIso c ∧ χ.app (G.obj K) ≫ F'.map c ≫ adj'.counit.app (S.obj K) =
        S.map (adj.counit.app K) := by
  let a := inv (χ.app (G.obj K)) ≫ S.map (adj.counit.app K)
  let c := (adj'.homEquiv _ _) a
  have he : F'.map c ≫ adj'.counit.app (S.obj K) = a := by
    exact (adj'.homEquiv _ _).symm_apply_apply a
  refine ⟨c, ⟨hc, ?_⟩, ?_⟩
  · rw [he]
    simp only [a, IsIso.hom_inv_id_assoc]
  · intro b hb
    apply (adj'.homEquiv _ _).symm.injective
    change F'.map b ≫ adj'.counit.app (S.obj K) =
      F'.map c ≫ adj'.counit.app (S.obj K)
    apply (cancel_epi (χ.app (G.obj K))).1
    rw [hb.2, he]
    simp only [a, IsIso.hom_inv_id_assoc]

private theorem residue_killed : (l : Padic.coefficientExtensionRing l E 1) = 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (l : Padic.coefficientExtensionIntegers l E) ∈
    Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
  rw [pow_one, hgen]
  apply (h.2.1 _).2
  have he := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
  change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
  rw [show (l : E) = algebraMap (Padic l) E (l : Padic l) by simp]
  change spectralNorm (Padic l) E (algebraMap (Padic l) E (l : Padic l)) < 1
  rw [he]
  exact Padic.norm_p_lt_one

private theorem residue_discrete :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E 1) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let I := Padic.coefficientExtensionIdeal l E 1
  apply QuotientAddGroup.discreteTopology (N := I.toAddSubgroup)
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hi : I = Padic.coefficientExtensionMaximalIdeal l E := by
    change Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1 = _
    rw [pow_one, hgen]
  have hs : (I.toAddSubgroup : Set (Padic.coefficientExtensionIntegers l E)) =
      {x : Padic.coefficientExtensionIntegers l E | ‖(x : E)‖ < 1} := by
    ext x
    change x ∈ I ↔ ‖(x : E)‖ < 1
    rw [hi]
    exact h.2.1 x
  rw [hs]
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

private theorem residue_open_image
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.quotientRing l E 1) U)))
    (hK : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) U K)
    (hTor : _root_.DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.quotientRing l E 1) j).obj K) ∧
    _root_.DerivedCategory.finiteTorAmplitude _
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.quotientRing l E 1) j).obj K) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Finite (Padic.coefficientExtensionRing l E 1) :=
    Padic.finite_coefficientExtensionRing l E 1 le_rfl
  have := residue_discrete l E
  obtain ⟨a, b, ht⟩ := hTor
  have ht' := ht.mono (min_le_left a b) (le_max_left b a)
  have hp : 0 < ringChar k := (Fact.out : (ringChar k).Prime).pos
  have hne : ringChar k ≠ l := Fact.out
  obtain ⟨d, _, hd⟩ := CondensedRing.finiteOpenDirectImage_constantModel_torAmplitude
    l (ringChar k) k hp hne (Padic.coefficientExtensionRing l E 1)
    ⟨1, le_rfl, by simpa only [pow_one] using residue_killed l E⟩ j
  obtain ⟨hbc, hta⟩ := hd (min a b) (max b a) (by omega) K hK ht'
  exact ⟨hbc, min a b, max b a + d, hta⟩

-- Normalize the two scalar adjunctions and the internal coefficient module categories.
/-- Integral open direct image is derived complete, commutes canonically with residue
reduction, and is bounded constructible; integral Dbc equals its finite-Tor subcategory.
The unique comparison is characterized by the usual pullback/reduction square and the
two geometric counits. This is the canonical coefficient-change (projection-formula) map. -/
theorem integral_open_direct_image
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) U K) :
    IsDerivedComplete l E X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      (∃! c :
          (AdicCompletion.derivedReduction l E X 0).obj
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ⟶
            (CondensedRing.moduleObjectDerivedPushforward
              (DerivedNakayama.quotientRing l E 1) j).obj
                ((AdicCompletion.derivedReduction l E U 0).obj K),
        IsIso c ∧
          (reductionPullbackMap l E j).app
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ≫
            (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory.map
              c ≫
            ((CondensedRing.derivedUpperStarLowerStarAdjunction
                (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
                  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                    (DerivedNakayama.quotientRing l E 1) j)).counit.app
              ((AdicCompletion.derivedReduction l E U 0).obj K) =
            (AdicCompletion.derivedReduction l E U 0).map
              (((CondensedRing.derivedUpperStarLowerStarAdjunction
                  (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
                    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                      (DerivedNakayama.integerRing l E) j)).counit.app K)) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
        (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X ⊓
          _root_.DerivedCategory.finiteTorAmplitude (AdicCompletion.Modules l E X)) := by
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian
    (U ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace
    (U ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let : IsNoetherian U := ⟨⟩
  let : IsNoetherian X := ⟨⟩
  have hlimits := internal_integral_direct_image_limits l E j
  have hχ : IsIso (reductionPullbackMap l E j) := hlimits.choose
  let := hχ
  have hpush := hlimits.choose_spec
  let adj := (CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.integerRing l E) j)
  let adj' := (CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.quotientRing l E 1) j)
  have hpushK := hpush K
  have hcomplete := hpushK.1
  have hmate := hpushK.2
  have hinputAll := internal_integral_residue_criterion l E U
  have hinput := hinputAll.1
  have houtputAll := internal_integral_residue_criterion l E X
  have houtput := houtputAll.1
  have htor' := houtputAll.2
  have hresK := (hinput K).mp hK
  have hcK := hresK.1
  have hrK := hresK.2.1
  have htK := hresK.2.2
  have hcomplete' := hcomplete hcK
  obtain ⟨c, hc, hunique⟩ := unique_mate adj adj'
    (AdicCompletion.derivedReduction l E X 0)
    (AdicCompletion.derivedReduction l E U 0) (reductionPullbackMap l E j) K hmate
  refine ⟨hcomplete', ⟨c, hc, hunique⟩, ?_, htor'⟩
  have hfinite := residue_open_image l E j k
    ((AdicCompletion.derivedReduction l E U 0).obj K) hrK htK
  have := hc.1
  have e := asIso c
  have hclosed := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.quotientRing l E 1) X).2.1
  let := hclosed
  exact (houtput _).mpr ⟨hcomplete',
    (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X).prop_of_iso
      e.symm hfinite.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hfinite.2⟩

end AlgebraicGeometry.ProEtale.IntegralOpenDirectImage
