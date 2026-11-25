/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteCoefficientRealization
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
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
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
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
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteHeartMonoidalPresentation
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteHeartConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Heart comparison for embedded finite-field coefficients

## References

* Stacks Tags 099L, 03ET, 00YV, 06YQ and 09AL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- The embedded finite-field presentation and the intrinsic presentation have a common
coefficient-sized section-module encoding. The embedded encoding is strong monoidal;
the specified derived realization is the induced functor under these encodings. -/
theorem finiteFieldPresentation
    (X : Scheme.{u}) [IsNoetherian X] (A : Type) [Field A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    let R := ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1, 0} A)
    letI := SheafOfModules.monoidalCategory R
    letI : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
    letI : HasDerivedCategory (Scheme.proEtaleRingModules X
        (Scheme.proEtaleConstantRing X (ULift.{u, 0} A))) := HasDerivedCategory.standard _
    ∃ E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (discreteObj A) X) ≌ ConstantCompletion.Mod R,
      ∃ H : Scheme.proEtaleRingModules X
          (Scheme.proEtaleConstantRing X (ULift.{u, 0} A)) ≌ ConstantCompletion.Mod R,
        ∃ (_ : E.functor.Additive) (_ : H.functor.Additive),
          Nonempty E.functor.Monoidal ∧
          Nonempty (finiteRealization X A ⋙ H.functor.mapDerivedCategory ≅
            E.functor.mapDerivedCategory) ∧
          ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj (discreteObj A) X))
            (N : Scheme.proEtaleRingModules X
              (Scheme.proEtaleConstantRing X (ULift.{u, 0} A))),
            (E.functor.obj M ≅ H.functor.obj N) →
            (IsConstantModelConstructible (discreteObj A) X M ↔
              Scheme.IsConstructibleProEtaleModuleSheaf X (ULift.{u, 0} A) N) := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let R := ConstantCompletion.constant
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1, 0} A)
  let := SheafOfModules.monoidalCategory R
  let : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Scheme.proEtaleRingModules X
      (Scheme.proEtaleConstantRing X (ULift.{u, 0} A))) := HasDerivedCategory.standard _
  obtain ⟨hI, H, hH, hm⟩ := finiteHeartMonoidalPresentation X A
  let := hI
  let := hH
  let S := Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (finiteScalarMap X A)
  let I := integralModelIntrinsicRealization X A
  have : S.IsEquivalence := finiteScalarExtension_isEquivalence X A
  have : I.IsEquivalence := hI
  let F := S ⋙ I
  have : F.IsEquivalence := inferInstance
  let E := F.asEquivalence.trans H
  have : E.functor.Additive := inferInstanceAs (F ⋙ H.functor).Additive
  refine ⟨E, H, inferInstance, hH, hm, ?_, ?_⟩
  · change Nonempty ((S.leftDerivedFunctor ⋙ I.rightDerivedFunctor) ⋙
      H.functor.mapDerivedCategory ≅ (F ⋙ H.functor).mapDerivedCategory)
    exact ⟨Functor.isoWhiskerRight
        (Functor.isoWhiskerRight S.leftDerivedFunctorIsoMapDerivedCategory
            I.rightDerivedFunctor ≪≫
          Functor.isoWhiskerLeft S.mapDerivedCategory I.rightDerivedFunctorIsoMapDerivedCategory)
        H.functor.mapDerivedCategory ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso S I)
        H.functor.mapDerivedCategory ≪≫
      Functor.mapDerivedCategoryCompIso F H.functor⟩
  · intro M N e
    have j : F.obj M ≅ N := H.functor.preimageIso e
    refine (finiteHeartConstructibility X A M).trans ?_
    rw [Scheme.proEtaleModuleRestriction_constructible_iff,
      Scheme.proEtaleModuleRestriction_constructible_iff]
    let k := (Scheme.proEtaleModuleRestriction X (ULift.{u, 0} A)).mapIso j
    exact ⟨fun h ↦ isConstructible_of_iso k h,
      fun h ↦ isConstructible_of_iso k.symm h⟩

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
