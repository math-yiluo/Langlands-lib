/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralTransport
public import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
public import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection
public import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullback
public import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
public import WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
public import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
public import WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent
public import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
import WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import WeilConjectures.AlgebraicGeometry.OrdinaryCommonQuotientTower
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option linter.privateModule false

/-! # Completion for embedded integral coefficients

Source: Stacks Project, Tags 099I, 099L, 099M and 0A07 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem smallModulesEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (IntegralModelsStacks.smallModules X R).IsEquivalence := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)
  let B := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (J := Scheme.ProEt.topology X)
    (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact inferInstanceAs
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor ⋙ e.inverse).IsEquivalence

private def smallRestrictionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Mod.comap f ⋙ IntegralModelsStacks.smallModules X R ≅
      IntegralModelsStacks.smallModules X S ⋙
        ConstantCompletion.res (IntegralModelsStacks.smallMap X f) := by
  dsimp only [IntegralModelsStacks.smallModules, IntegralModelsStacks.smallMap]
  let e := CondensedRing.sectionModuleComapIso X f
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      exact (((e.hom.app M).val.app (op (AsSmall.down.obj U.unop))).hom.map_smul r m).symm
    · intro U V g
      ext m
      rfl
  · intro M N g
    ext U m
    rfl

attribute [local irreducible] IntegralModelsStacks.smallDerivedObject
  IntegralModelsStacks.smallModules IntegralModelsStacks.smallMap
  ConstantCompletion.kernelIdeal RingedSiteIdeal.extension

end AlgebraicGeometry.ProEtale
