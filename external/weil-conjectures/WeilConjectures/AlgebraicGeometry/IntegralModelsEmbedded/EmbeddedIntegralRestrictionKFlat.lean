/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteCoefficientRealization
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedScalarFlat
import all WeilConjectures.AlgebraicGeometry.IntegralCoefficientSquare.IntegralCoefficientSquareNormalizationSupplement
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # K-flat restriction of integral scalars

## References

* Stacks Tags 06YN, 06YY and 03ER
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem flat_from_small (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u + 1, u + 1, u + 1}
      (R := (AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (Scheme.ProEt.topology X)).obj R)
      ((SheafOfModules.pushforward (F := AsSmall.down)
        (J := Scheme.coefficientProEtaleModelTopology.{u, u} X) (𝟙 _)).obj M)) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} M := by
  let d := (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt)
  let a := (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} X)
  let R' := (d.sheafPushforwardContinuous CommRingCat.{u + 1}
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj R
  have h :=
    (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u + 1, u + 1, u + 1}
      R' _).mp hM
  apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1} R M).mpr
  intro U n b s hs
  obtain ⟨S, hS, hlocal⟩ := h (a.obj U) n b s hs
  refine ⟨S.functorPushforward d, ?_, ?_⟩
  · exact (Functor.mem_inducedTopology_iff_of_isCoverDense d
      (Scheme.ProEt.topology X) S).mp hS
  · intro V f hf
    have hg : S (a.map f) :=
      (Sieve.mem_functorPushforward_iff_of_full_of_faithful d S (a.map f)).mp hf
    exact hlocal (a.obj V) (a.map f) hg

attribute [-instance] integralModel_coefficientMonObj in
/-- Restriction of embedded integral scalars preserves K-flat cochain complexes. -/
theorem embeddedIntegralRestrictionKFlat
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X]
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Mod.comap (scalarMap ℓ E X)).mapHomologicalComplex (.up ℤ)).obj P) := by
  let φ := scalarMap ℓ E X
  let R := condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X
  let B := integralCoefficientObject X ℓ E
  let J := Scheme.ProEt.topology X
  let eR := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let eB := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J B
  let α := CondensedRing.sectionRingMap X φ
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
  let β := CondensedRing.sectionModuleComapIso X φ
  let b := β.app (Mod.regular B) ≪≫ U.mapIso (CondensedRing.sectionModuleRegularIso X B)
  have hsmall := integralModelsEmbeddedScalarFlat ℓ E π hπ X
  have hsf := (flat_iff_flatOnSite _).mp hsmall
  have hb : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (eR.functor.obj
      ((Mod.comap φ).obj (Mod.regular B))) := by
    apply flat_from_small.{u} X (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
    let V := SheafOfModules.pushforward (F := AsSmall.down)
      (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (K := Scheme.ProEt.topology X)
      (𝟙 ((AsSmall.down.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) J).obj
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))))
    change SheafOfModules.IsFlatOnSite
      (R := (AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) J).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))
      (V.obj (U.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B))))) at hsf
    exact SheafOfModules.flatOnSite_of_iso
      ((AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) J).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))
      (V.mapIso b).symm hsf
  have hb' : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
      (U.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B)))) := by
    exact SheafOfModules.flatOnSite_of_iso.{u + 1, u + 1, u}
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R) b hb
  have hPi := (InternalAbelianSheafModule.comparison_kflat.{u + 1, u + 1, u} J B P).mp
    ((IntegralCoefficientSquare.internal_kflat_iff P).mpr hP)
  have hk := (SheafOfModules.isKFlat_restrictScalars_of_flat.{u + 1, u, u + 1} α hb'
    ((eB.functor.mapHomologicalComplex (.up ℤ)).obj P) hPi).1
  let d := (NatIso.mapHomologicalComplex β (.up ℤ)).app P
  apply (IntegralCoefficientSquare.internal_kflat_iff _).mp
  apply (InternalAbelianSheafModule.comparison_kflat.{u + 1, u + 1, u} J R _).mpr
  exact SheafOfModules.kFlat_iso_independent.{u + 1, u + 1, u}
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R) d.symm hk

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
