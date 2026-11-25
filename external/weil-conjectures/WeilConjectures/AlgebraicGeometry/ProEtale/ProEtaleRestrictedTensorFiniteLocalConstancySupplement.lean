/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationTensorComplex
import all WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.LocallyConstantTensor
import all WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import all WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import all Mathlib.RingTheory.Finiteness.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Sites.Pretopology
import all Mathlib.RingTheory.Noetherian.Defs
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.AlgebraicGeometry.SiteFiniteFreeTruncationModels
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.Algebra.Category.ModuleCat.Free
import all WeilConjectures.AlgebraicGeometry.SiteBoundedTruncationModels
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import all WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import all WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import all WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import all WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import all WeilConjectures.Algebra.Homology.SmoothPurity.ConstantLocalModuleHomSupplement
import all WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import all WeilConjectures.CategoryTheory.Site.SiteConstantModuleUnitSupplement
import all Mathlib.Algebra.Module.FinitePresentation
import all WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import all WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.ConstantForget
import all Mathlib.RingTheory.Noetherian.Basic
import all WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import all WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import all WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.CategoryTheory.Abelian.Exact
import all WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import all WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Mathlib.RingTheory.Finiteness.Cardinality
import all WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.LinearAlgebra.StdBasis
import all WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.RingTheory.Finiteness.Basic
import all WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Homology.Additive
import all Mathlib.Data.Int.Interval
import all WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import all WeilConjectures.RingTheory.RingPseudoCoherent
import all WeilConjectures.RingTheory.FiniteFreeResolution
import all WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import all Mathlib.Algebra.Homology.Single
import all WeilConjectures.RingTheory.PseudoCoherentIffAllM
import all WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import all WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import all WeilConjectures.CategoryTheory.TruncationTriangle
import all Mathlib.Algebra.Category.ModuleCat.Projective
import all Mathlib.CategoryTheory.Abelian.Projective.Extend
import all WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import all WeilConjectures.AlgebraicGeometry.SiteTensorLocalModelComparison
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.Algebra.Homology.SliceTensorNatural
import all WeilConjectures.Algebra.Homology.SliceModuleSheafification
import all Mathlib.Topology.Sheaves.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import all Mathlib.Algebra.Homology.ShortComplex.Basic
import all Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import all WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import all Mathlib.CategoryTheory.Sites.LocallyInjective
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import all Mathlib.RingTheory.TensorProduct.Finite
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

/-!
# Finite local constancy of a restricted derived tensor

## References

* Stacks Project, Cohomology on Sites, Tags 094H and 07A4
* Stacks Project, Cohomology on Sites, Tag 094H, and Tag 07A4
-/

@[expose] public section

universe u
set_option autoImplicit false
-- Honor the sealed tensor constructions despite the package's legacy default.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 256
-- Check each sealed comparison before elaborating its consumers.
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

section Proof

-- Build total tensors directly from countable colimits, avoiding diagram-wide search.
private instance tensorTotal {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasColimitsOfSize.{0, 0} C]
    (P Q : CochainComplex C ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor C) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (inferInstance : HasColimitsOfSize.{0, 0} C) _ _) _

section TensorTransport
universe u₁ u₂ v₁ v₂
open CategoryTheory.MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]

omit [MonoidalCategory C] [MonoidalPreadditive C] [HasColimitsOfSize.{0, 0} C] in
private theorem acyclic_iso {P Q : CochainComplex C ℤ} (e : P ≅ Q) (h : P.Acyclic) :
    Q.Acyclic := fun i ↦ (h i).of_iso e

omit [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D] in
private theorem acyclic_equivalence (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (P : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj P).Acyclic ↔ P.Acyclic := by
  constructor
  · intro h i
    exact (P.sc i).exact_map_iff_of_faithful F |>.1 (h i)
  · intro h i
    exact (P.sc i).exact_map_iff_of_faithful F |>.2 (h i)

private theorem kflat_equivalence (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) (P : CochainComplex C ℤ) :
    (∀ Z : CochainComplex D ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z ((F.mapHomologicalComplex (.up ℤ)).obj P)
        (curriedTensor D)).Acyclic) ↔
    (∀ Z : CochainComplex C ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (curriedTensor C)).Acyclic) := by
  let W := F.mapHomologicalComplex (.up ℤ)
  have total (Z : CochainComplex C ℤ) :=
    AlgebraicGeometry.ProEtale.tensorComplexTransportAux F e Z P
  constructor
  · intro h Z hz
    apply (acyclic_equivalence F _).mp
    obtain ⟨q⟩ := total Z
    exact acyclic_iso q.symm (h (W.obj Z) ((acyclic_equivalence F Z).mpr hz))
  · intro h Z hz
    have : W.IsEquivalence :=
      (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
    let V := W.asEquivalence
    let Z' := V.inverse.obj Z
    have hZ' : Z'.Acyclic :=
      (acyclic_equivalence F Z').mp (acyclic_iso (V.counitIso.app Z).symm hz)
    obtain ⟨q⟩ := total Z'
    have hq := acyclic_iso q ((acyclic_equivalence F _).mpr (h Z' hZ'))
    let t := (curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
    exact acyclic_iso ((CategoryTheory.Functor.mapIso t (V.counitIso.app Z)).app _)
      hq

@[no_expose, irreducible]
private noncomputable def tensor_inverse (F : C ⥤ D) [F.IsEquivalence]
    (G : D ⥤ C) (c : G ⋙ F ≅ 𝟭 D)
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) :
    tensor D ⋙ G ≅ G.prod G ⋙ tensor C := by
  let W := (Functor.whiskeringRight (D × D) C D).obj F
  exact W.preimageIso
    (Functor.isoWhiskerLeft (tensor D) c ≪≫
      (Functor.leftUnitor (tensor D)).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c.symm c.symm) (tensor D) ≪≫
      Functor.isoWhiskerLeft (G.prod G) e.symm)

@[no_expose, irreducible]
private noncomputable def tensor_comp (F : C ⥤ D)
    {E : Type*} [Category E] [MonoidalCategory E] (G : D ⥤ E)
    (eF : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (eG : tensor D ⋙ G ≅ G.prod G ⋙ tensor E) :
    tensor C ⋙ F ⋙ G ≅ (F ⋙ G).prod (F ⋙ G) ⋙ tensor E :=
  Functor.isoWhiskerRight eF G ≪≫ Functor.isoWhiskerLeft (F.prod F) eG

end TensorTransport

attribute [local instance] Sheaf.monoidalCategory

section SmallCoefficients
universe s
variable {C : Type s} [Category.{s} C] (J : GrothendieckTopology C)
  (B : Type s) [CommRing B]

private noncomputable abbrev smallR := (sheafCompose J
  (forget₂ CommRingCat.{s} RingCat.{s})).obj
    ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B))
private noncomputable abbrev smallScalar :
    (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ (smallR J B).obj := Functor.whiskerRight
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
  (forget₂ CommRingCat.{s} RingCat.{s})
private instance smallScalar_injective : Presheaf.IsLocallyInjective J (smallScalar J B) :=
  SheafOfModules.constantCommRingUnit_locallyInjective J B

private instance smallScalar_surjective : Presheaf.IsLocallySurjective J (smallScalar J B) :=
  SheafOfModules.constantCommRingUnit_locallySurjective J B

private noncomputable abbrev smallF := moduleExtension J B (smallR J B) (smallScalar J B)
private noncomputable abbrev smallG := moduleRestriction J B (smallR J B) (smallScalar J B)

@[instance_reducible]
private noncomputable instance smallConstMonoidal :
    MonoidalCategory (PresheafOfModules.{s}
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{s}
    (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat)))

attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

private noncomputable abbrev smallMonoidal :=
  @SheafOfModules.monoidalCategory.{s, s, s} C _ J _
    ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)) _ _
    (SheafOfModules.isMonoidal_W
      ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)))

attribute [local instance] smallMonoidal

private theorem smallF_tensor :
    Nonempty (tensor (Sheaf J (ModuleCat.{s} B)) ⋙ smallF J B ≅
      (smallF J B).prod (smallF J B) ⋙ tensor (SheafOfModules.{s} (smallR J B))) := by
  let E := constantModulePresheaf J B
  let S := PresheafOfModules.sheafification.{s} (R := smallR J B) (smallScalar J B)
  let U := sheafToPresheaf J (ModuleCat.{s} B)
  let L := presheafToSheaf J (ModuleCat.{s} B)
  let F := smallF J B
  let : MonoidalCategory (SheafOfModules.{s} (smallR J B)) := smallMonoidal J B
  let t : E ⋙ S ⟶ L ⋙ F :=
    Functor.whiskerRight (sheafificationAdjunction J (ModuleCat.{s} B)).unit (E ⋙ S)
  have : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    rw [← MorphismProperty.isomorphisms.iff]
    change ((MorphismProperty.isomorphisms _).inverseImage S) _
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    change J.W (Functor.whiskerRight (toSheafify J P)
      (forget₂ (ModuleCat.{s} B) AddCommGrpCat.{s}))
    let : J.PreservesSheafification (forget₂ (ModuleCat.{s} B) AddCommGrpCat.{s}) :=
      Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂CoinduceAdj B)
    exact J.W_of_preservesSheafification _ _ (J.W_toSheafify P)
  let h : E ⋙ S ≅ L ⋙ F := asIso t
  let c := asIso (sheafificationAdjunction J (ModuleCat.{s} B)).counit
  let e : U.prod U ⋙ tensor _ ⋙ L ≅ tensor _ :=
    Functor.isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c c) (tensor _)
  let eE : tensor _ ⋙ E ≅ E.prod E ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦
      PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
        intro U V f
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        rfl)) (by
          intro MN MN' fg
          ext U : 1
          apply ModuleCat.MonoidalCategory.tensor_ext
          intro x y
          rfl)
  obtain ⟨eS, _⟩ := PresheafOfModules.exists_sheafificationTensorIso
    (O := (Functor.const Cᵒᵖ).obj (CommRingCat.of B)) (smallScalar J B)
  exact ⟨(Functor.isoWhiskerRight e F).symm ≪≫
    Functor.isoWhiskerLeft (U.prod U ⋙ tensor _) h.symm ≪≫
    Functor.isoWhiskerLeft (U.prod U) (Functor.isoWhiskerRight eE S) ≪≫
    Functor.isoWhiskerLeft ((U ⋙ E).prod (U ⋙ E)) eS.symm⟩

private theorem small_models (F : SheafOfModules.{s} (smallR J B)) :
    SheafOfModules.IsLocallyConstantFiniteType J B F ↔
    AlgebraicGeometry.Scheme.ProFiniteModels.fixedModels J B ((smallG J B).obj F) := by
  let R := smallR J B
  let α := smallScalar J B
  let G := smallG J B
  let c := SheafOfModules.strictPerfectConstantPresheaf (C := C) B ⋙
    PresheafOfModules.sheafification (R := R) α
  let ec := moduleRestrictionConstantIso J B R α
  have hi (U : C) (M : ModuleCat.{s} B) :
      Nonempty (F.over U ≅ (c.obj M).over U) ↔
      Nonempty ((G.obj F).over U ≅ (constantSheaf (J.over U) _).obj M) := by
    let αU := Functor.whiskerLeft (Over.forget U).op α
    have hαi : Presheaf.IsLocallyInjective (J.over U) αU := by
      dsimp only [αU]
      exact Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α
    have hαs : Presheaf.IsLocallySurjective (J.over U) αU := by
      dsimp only [αU]
      exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α
    let GU := @moduleRestriction.{s} (Over U) _ (J.over U) B _ (R.over U)
      αU hαi hαs
    let : GU.IsEquivalence := @moduleRestriction_isEquivalence.{s} (Over U) _
      (J.over U) B _ (R.over U) αU hαi hαs
    let hGU (N : SheafOfModules R) : GU.obj (N.over U) ≅ (G.obj N).over U :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ by
        dsimp only [GU, G, smallG, moduleRestriction, moduleRestrictionObj]
        exact Iso.refl _) (by intro V W f; ext x; rfl))
    let q : GU.obj ((c.obj M).over U) ≅ (constantSheaf (J.over U) _).obj M :=
      hGU (c.obj M) ≪≫ (J.overPullback _ U).mapIso (ec.app M) ≪≫
        (constantSheafOverIso J (ModuleCat.{s} B) U M).symm
    constructor
    · rintro ⟨e⟩
      exact ⟨(hGU F).symm ≪≫ GU.mapIso e ≪≫ q⟩
    · rintro ⟨e⟩
      exact ⟨GU.preimageIso (hGU F ≪≫ e ≪≫ q.symm)⟩
  constructor
  all_goals
    intro h V
    obtain ⟨S, hS, h⟩ := h V
    refine ⟨S, hS, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := h U f hf
    first
    | exact ⟨M, hM, (hi U M).mp he⟩
    | exact ⟨M, hM, (hi U M).mpr he⟩

private theorem small_tensor [HasPullbacks C]
    (P Q : CochainComplex (SheafOfModules.{s} (smallR J B)) ℤ)
    (hp : CochainComplex.IsAcyclicTensorKFlat (R :=
      (constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)) P)
    (hq : CochainComplex.IsAcyclicTensorKFlat (R :=
      (constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)) Q)
    (hbP : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (P.homology j))
    (hbQ : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (Q.homology j))
    (hlP : ∀ j, SheafOfModules.IsLocallyConstantFiniteType J B (P.homology j))
    (hlQ : ∀ j, SheafOfModules.IsLocallyConstantFiniteType J B (Q.homology j))
    [IsNoetherianRing B] (i : ℤ) :
    let := SheafOfModules.monoidalCategory
      ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B))
    SheafOfModules.IsLocallyConstantFiniteType J B
      ((CochainComplex.mapBifunctor P Q (curriedTensor _)).homology i) := by
  have hJ : J.toPrecoverage.toGrothendieck = J := by
    apply le_antisymm J.toGrothendieck_toPrecoverage_le
    intro U S hS
    simpa only [Sieve.generate_sieve] using
      J.toPrecoverage.generate_mem_toGrothendieck
        ((J.arrows_mem_toPrecoverage_iff S).mpr hS)
  revert P Q
  let work := fun (J' : GrothendieckTopology C) ↦
    (∀ (P Q : CochainComplex (SheafOfModules.{s} (smallR J' B)) ℤ),
      CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf J' CommRingCat.{s}).obj (CommRingCat.of B)) P →
      CochainComplex.IsAcyclicTensorKFlat (R :=
        (constantSheaf J' CommRingCat.{s}).obj (CommRingCat.of B)) Q →
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (P.homology j)) →
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (Q.homology j)) →
      (∀ j, SheafOfModules.IsLocallyConstantFiniteType J' B (P.homology j)) →
      (∀ j, SheafOfModules.IsLocallyConstantFiniteType J' B (Q.homology j)) →
      let := SheafOfModules.monoidalCategory
        ((constantSheaf J' CommRingCat.{s}).obj (CommRingCat.of B))
      SheafOfModules.IsLocallyConstantFiniteType J' B
        ((CochainComplex.mapBifunctor P Q (curriedTensor _)).homology i))
  change work J
  rw [← hJ]
  intro P Q hp hq hbP hbQ hlP hlQ
  let D := SheafOfModules.{s} (smallR J.toPrecoverage.toGrothendieck B)
  let := HasDerivedCategory.standard D
  have e (V : CochainComplex D ℤ) (j : ℤ) :=
    (DerivedCategory.homologyFunctorFactors D j).app V
  apply SheafOfModules.locallyConstantFiniteType_derivedTensor J.toPrecoverage B
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    ?_ ?_ ?_ ?_ P Q hp hq (Iso.refl _) (Iso.refl _) i
  · obtain ⟨b, hb⟩ := hbP
    exact ⟨b, fun j hj ↦ (hb j hj).of_iso (e P j)⟩
  · obtain ⟨b, hb⟩ := hbQ
    exact ⟨b, fun j hj ↦ (hb j hj).of_iso (e Q j)⟩
  · intro j
    exact SheafOfModules.locallyConstantFiniteType_of_iso _ _ (e P j) (hlP j)
  · intro j
    exact SheafOfModules.locallyConstantFiniteType_of_iso _ _ (e Q j) (hlQ j)

end SmallCoefficients

attribute [-instance] smallConstMonoidal

namespace AlgebraicGeometry.Scheme

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense

@[no_expose]
private noncomputable def siteEncoding (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).sheafCongr
    (ProEt.topology X) (proEtaleModelTopology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))

private theorem siteTensor (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Nonempty (tensor _ ⋙ (siteEncoding X A).functor ≅
      (siteEncoding X A).functor.prod (siteEncoding X A).functor ⋙ tensor _) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let J := ProEt.topology X
  let K := proEtaleModelTopology X
  let d : proEtaleSiteModel X ⥤ X.ProEt := AsSmall.down
  let H := (siteEncoding X A).functor
  let U := sheafToPresheaf J B
  let U' := sheafToPresheaf K B
  let L := presheafToSheaf J B
  let L' := presheafToSheaf K B
  let V := (Functor.whiskeringLeft _ _ B).obj d.op
  let c := asIso (sheafificationAdjunction J B).counit
  let c' := asIso (sheafificationAdjunction K B).counit
  let e : U.prod U ⋙ tensor _ ⋙ L ≅ tensor _ :=
    Functor.isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c c) (tensor _)
  let e' : U'.prod U' ⋙ tensor _ ⋙ L' ≅ tensor _ :=
    Functor.isoWhiskerLeft (U'.prod U') (Functor.Monoidal.μNatIso L').symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c' c') (tensor _)
  let h : L ⋙ H ≅ V ⋙ L' :=
    (d.pushforwardContinuousSheafificationCompatibility B K J).symm
  let t : tensor _ ⋙ V ≅ V.prod V ⋙ tensor _ := Iso.refl _
  exact ⟨(Functor.isoWhiskerRight e H).symm ≪≫
    Functor.isoWhiskerLeft (U.prod U ⋙ tensor _) h ≪≫
    Functor.isoWhiskerLeft (U.prod U) (Functor.isoWhiskerRight t L') ≪≫
    Functor.isoWhiskerLeft (H.prod H) e'⟩

private instance intrinsicMonoidalW (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ((ProEt.topology X).W.inverseImage (PresheafOfModules.toPresheaf.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).IsMonoidal :=
  SheafOfModules.isMonoidal_W_separateHomUniverse.{u + 1, u} (R := R)

@[no_expose, instance_reducible]
private noncomputable instance intrinsicRTMonoidal (X : Scheme.{u}) (A : Type u)
    [CommRing A] : MonoidalCategory (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing X A)

private theorem restrictionTensor (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    let : MonoidalCategory (proEtaleRingModules X (proEtaleConstantRing X A)) :=
      SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing X A)
    Nonempty (tensor (proEtaleRingModules X (proEtaleConstantRing X A)) ⋙
      proEtaleModuleRestriction X A ≅
      (proEtaleModuleRestriction X A).prod (proEtaleModuleRestriction X A) ⋙
        tensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) := by
  let F := ProEtale.finiteCoefficientIntrinsicRealization X A
  let G := proEtaleModuleRestriction X A
  let := (ProEtale.finiteCoefficientIntrinsicRealization_exact X A).1
  let : MonoidalCategory (proEtaleRingModules X (proEtaleConstantRing X A)) :=
    SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing X A)
  let : Presheaf.IsLocallyInjective (ProEt.topology X)
      (proEtaleModuleScalarUnit X A) := (proEtaleConstantRingUnit_locallyBijective X A).1
  let : Presheaf.IsLocallySurjective (ProEt.topology X)
      (proEtaleModuleScalarUnit X A) := (proEtaleConstantRingUnit_locallyBijective X A).2
  let c : G ⋙ F ≅ 𝟭 _ := NatIso.ofComponents
    (fun M ↦ by
      have hc : IsIso (PresheafOfModules.sheafificationAdjunction.{u + 1}
          (proEtaleModuleScalarUnit X A)).counit := inferInstance
      exact (asIso (PresheafOfModules.sheafificationAdjunction.{u + 1}
        (proEtaleModuleScalarUnit X A)).counit).app M)
    (by intro M N f; exact (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (proEtaleModuleScalarUnit X A)).counit.naturality f)
  exact ⟨tensor_inverse F G c (ProEtale.intrinsicTensorNatIso X A).some⟩

private def finiteLocal (X : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) : Prop :=
  IsLocallyConstantProEtaleModuleSheaf X A F ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A) F)

private theorem finiteLocal_iso (X : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules X (proEtaleConstantRing X A)} (e : F ≅ G)
    (hF : finiteLocal X A F) : finiteLocal X A G := by
  constructor
  · obtain ⟨I, U, f, hf, h⟩ := hF.1
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨eM⟩⟩ := h i
    exact ⟨M, ⟨((SheafOfModules.overFunctor _ (U i)).mapIso e).symm ≪≫ eM⟩⟩
  · intro Ω _ _ x
    exact @Finite.of_equiv _ _ (hF.2 Ω x)
      (Equiv.ofBijective
        ((geometricRingModuleStalkFunctor x (proEtaleConstantRing X A)).mapIso e).hom
        (ConcreteCategory.bijective_of_isIso _))

private theorem finiteLocal_fixedModels (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) :
    finiteLocal X A F ↔ ProFiniteModels.fixedModels (ProEt.topology X)
      (ULift.{u + 1, u} A) ((proEtaleModuleRestriction X A).obj F) := by
  classical
  let B := ULift.{u + 1, u} A
  let J := ProEt.topology X
  let F' := (proEtaleModuleRestriction X A).obj F
  constructor
  · intro h U
    obtain ⟨I₀, W₀, g₀, hg₀, h₀⟩ := (finiteLocal_iff.{u} X A F).mpr h
    obtain ⟨I, V, g, hg, he⟩ := ProEtale.finiteModels_over B F'
      ⟨I₀, W₀, g₀, hg₀, fun i ↦ by
        obtain ⟨M, hM, e⟩ := h₀ i
        exact ⟨M, Module.finite_of_finite B, e⟩⟩
    let a : U ⟶ ProEt.mk (𝟙 X) :=
      MorphismProperty.Over.homMk U.hom (Category.comp_id _)
    let W (i : I) := pullback a (g i)
    let p (i : I) : W i ⟶ U := pullback.fst _ _
    let t (i : I) : W i ⟶ V i := pullback.snd _ _
    have hc := Precoverage.mem_coverings_of_isPullback g hg a p t
      (fun i ↦ IsPullback.of_hasPullback _ _)
    refine ⟨Sieve.ofArrows W p, (ProEt.precoverage X).generate_mem_toGrothendieck hc, ?_⟩
    intro Z f hf
    obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff W p f).mp hf
    obtain ⟨M, hM, ⟨e⟩⟩ := he i
    have : Finite M := hM
    let C := (constantSheaf J (ModuleCat.{u + 1} B)).obj M
    let E := (Over.map (k ≫ t i)).sheafPushforwardContinuous
      (ModuleCat.{u + 1} B) (J.over Z) (J.over (V i))
    exact ⟨M, Module.Finite.of_finite, ⟨
      (F'.pushforwardOverMapIso (k ≫ t i)).symm ≪≫
      E.mapIso (e ≪≫ constantSheafOverIso J (ModuleCat.{u + 1} B) (V i) M) ≪≫
      C.pushforwardOverMapIso (k ≫ t i) ≪≫
      (constantSheafOverIso J (ModuleCat.{u + 1} B) Z M).symm⟩⟩
  · intro h
    obtain ⟨S, hS, he⟩ := h (ProEt.mk (𝟙 X))
    obtain ⟨R, hR, hRS⟩ :=
      (ProEt.precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
    obtain ⟨I, U, f, rfl⟩ := R.exists_eq_ofArrows
    have hm (i : I) := he (U i) (f i) (hRS _ _ (Presieve.ofArrows.mk i))
    apply (finiteLocal_iff.{u} X A F).mp
    have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        proetalePrecoverage X := by
      rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hR
      change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
        proetalePrecoverage X at hR
      have hw (i : I) : (f i).left = (U i).hom := by
        have hw := MorphismProperty.Over.w (f i)
        change (f i).left ≫ 𝟙 X = (U i).hom at hw
        exact (Category.comp_id _).symm.trans hw
      change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
        proetalePrecoverage X at hR
      simp only [hw] at hR
      exact hR
    refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hm i
    have := hM
    have : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
        (ProEt.topology (U i).left) (J.over (U i)) := ProEt.sliceDense X (U i)
    let S := (ProEt.sliceEquiv X (U i)).sheafCongr
      (J.over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
    let r : S.functor.obj (F'.over (U i)) ≅
        (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F' :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
      (J.over (U i)) (ProEt.topology (U i).left)
      (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app M
    exact ⟨M, hM, ⟨
      (ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F' ≪≫
      r.symm ≪≫ S.functor.mapIso e ≪≫ c⟩⟩

private theorem finiteLocal_zero (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) (hF : IsZero F) :
    finiteLocal X A F := by
  have : IsNoetherianRing A := inferInstance
  apply (finiteLocal_fixedModels X A F).mpr
  exact (ProFiniteModels.intrinsic_fixedModels X A F).mp
    (IsFinitelyPresentedLocallyConstantProEtaleModule_of_isZero hF)

@[no_expose]
private noncomputable def encoding (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  proEtaleModuleRestriction X A ⋙ (siteEncoding X A).functor ⋙
    smallF (proEtaleModelTopology X) (ULift.{u + 1, u} A)

private noncomputable instance encoding_equiv (X : Scheme.{u}) (A : Type u)
    [CommRing A] : (encoding X A).IsEquivalence := by
  let := proEtaleModuleRestriction_isEquivalence X A
  change (proEtaleModuleRestriction X A ⋙ (siteEncoding X A).functor ⋙
    smallF (proEtaleModelTopology X) (ULift.{u + 1, u} A)).IsEquivalence
  let : (smallF (proEtaleModelTopology X) (ULift.{u + 1, u} A)).IsEquivalence := {}
  infer_instance

private noncomputable instance encoding_additive (X : Scheme.{u}) (A : Type u)
    [CommRing A] : (encoding X A).Additive :=
  Functor.additive_of_preserves_binary_products (encoding X A)

private theorem finiteLocal_encoding (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) :
    finiteLocal X A F ↔ SheafOfModules.IsLocallyConstantFiniteType
      (proEtaleModelTopology X) (ULift.{u + 1, u} A) ((encoding X A).obj F) := by
  unfold encoding
  rw [finiteLocal_fixedModels, small_models]
  rw [ProFiniteModels.fixedModels_asSmall]
  let J := proEtaleModelTopology X
  let B := ULift.{u + 1, u} A
  let N := (siteEncoding X A).functor.obj ((proEtaleModuleRestriction X A).obj F)
  let e := (moduleRestrictionUnit J B (smallR J B) (smallScalar J B)).app N
  have hi {M N : Sheaf J (ModuleCat.{u + 1} B)} (q : M ≅ N)
      (h : ProFiniteModels.fixedModels J B M) : ProFiniteModels.fixedModels J B N := by
    intro U
    obtain ⟨S, hS, h⟩ := h U
    refine ⟨S, hS, fun V f hf ↦ ?_⟩
    obtain ⟨W, hW, ⟨g⟩⟩ := h V f hf
    exact ⟨W, hW, ⟨((J.overPullback _ V).mapIso q).symm ≪≫ g⟩⟩
  exact ⟨hi e.symm, hi e⟩

section EncodingTensor
-- Comparing tensor functors needs only the API, never the localization construction.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

private theorem encoding_tensor (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    let mR := intrinsicRTMonoidal X A
    let mS := smallMonoidal (proEtaleModelTopology X) (ULift.{u + 1, u} A)
    Nonempty (@tensor _ _ mR ⋙ encoding X A ≅
      (encoding X A).prod (encoding X A) ⋙ @tensor _ _ mS) := by
  let J := proEtaleModelTopology X
  let B := ULift.{u + 1, u} A
  let mR := intrinsicRTMonoidal X A
  let mS := smallMonoidal J B
  let U := proEtaleModuleRestriction X A
  let V := (siteEncoding X A).functor
  let W := smallF J B
  let tR := @tensor _ _ mR
  let tS := @tensor _ _ mS
  let tF := tensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
  let tG := tensor (Sheaf J (ModuleCat.{u + 1} B))
  have hU : tR ⋙ U ≅ U.prod U ⋙ tF := (restrictionTensor X A).some
  have hV : tF ⋙ V ≅ V.prod V ⋙ tG := (siteTensor X A).some
  have hW : tG ⋙ W ≅ W.prod W ⋙ tS := (smallF_tensor J B).some
  let : MonoidalCategory (proEtaleRingModules X (proEtaleConstantRing X A)) := mR
  let : MonoidalCategory (SheafOfModules (smallR J B)) := mS
  have hVW : tF ⋙ V ⋙ W ≅ (V ⋙ W).prod (V ⋙ W) ⋙ tS :=
    tensor_comp V W hV hW
  unfold encoding
  exact ⟨tensor_comp U (V ⋙ W) hU hVW⟩

end EncodingTensor

attribute [local irreducible] encoding siteEncoding

-- Use tensor comparison lemmas without reducing their localized monoidal structures.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

attribute [-instance] intrinsicRTMonoidal

private theorem pullback_kflat {T X : Scheme.{u}} (a : X ⟶ T)
    (A : Type u) [CommRing A]
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hp : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T A) P)
    (hflat : ∀ n, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing T A)) (P.X n))) :
    CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing X A)
      (((proEtaleConstantModulePullbackFunctor a A).mapHomologicalComplex (.up ℤ)).obj P) := by
  let R := proEtaleConstantRing T A
  let S := proEtaleConstantRing X A
  have := constantComparison_isIso a A
  let c := asIso (proEtaleCoefficientInverseImageMap a A)
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists a R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage a (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage a (𝟙 T)).2.2.2.1
  let F := I.modules ⋙ proEtaleRingExtension a R S c
  have hF : F = proEtaleConstantModulePullbackFunctor a A := by
    dsimp only [F]; rw [hI]; rfl
  have : F.Additive := by rw [hF]; infer_instance
  have hobj (M) : F.obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} c.hom (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom
        (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm := by
    intro M N f
    change (proEtaleRingExtension a R S c).map (I.modules.map f) =
      𝟙 _ ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom
        (I.modules.obj M) (I.modules.map f) ≫ 𝟙 _
    unfold proEtaleRingExtension proEtaleRingExtensionPresheaf
    simp only [Functor.comp_map, Category.id_comp, Category.comp_id]
    rfl
  have hf (n) : SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) (P.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hflat n)
  have hp' := SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage a (Type (u + 1)))
    (proEtaleSheafDirectImage a (Type (u + 1)))
    (proEtaleSheafAdjunction a (Type (u + 1))) I c.hom F hobj hmap P hp hf
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
  simpa only [hF] using hp'.1

attribute [local instance] intrinsicRTMonoidal

private instance intrinsicPreadditive (X : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalPreadditive (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  SheafOfModules.monoidalPreadditive_kfg.{u + 1, u} (proEtaleConstantRing X A)

private instance intrinsicCountableColimits (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasColimitsOfSize.{0, 0} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  inferInstance

private theorem intrinsic_tensor (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (P Q : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (hp : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing X A) P)
    (hq : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing X A) Q)
    (hbP : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (P.homology j))
    (hbQ : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (Q.homology j))
    (hlP : ∀ j, finiteLocal X A (P.homology j))
    (hlQ : ∀ j, finiteLocal X A (Q.homology j)) (i : ℤ) :
    finiteLocal X A ((CochainComplex.mapBifunctor P Q (curriedTensor _)).homology i) := by
  let R := proEtaleConstantRing X A
  let J := proEtaleModelTopology X
  let B := ULift.{u + 1, u} A
  let S := (constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of B)
  let : MonoidalCategory (SheafOfModules (smallR J B)) := smallMonoidal J B
  have : MonoidalPreadditive (SheafOfModules (smallR J B)) :=
    SheafOfModules.monoidalPreadditive_kfg.{u + 1, u + 1} S
  let F := encoding X A
  let W := F.mapHomologicalComplex (.up ℤ)
  have : HasPullbacks (proEtaleSiteModel X) :=
    Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt)
  have e (V : CochainComplex (proEtaleRingModules X R) ℤ) (j : ℤ) :
      (W.obj V).homology j ≅ F.obj (V.homology j) := (V.sc j).mapHomologyIso F
  have hb (V : CochainComplex (proEtaleRingModules X R) ℤ)
      (h : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (V.homology j)) :
      ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((W.obj V).homology j) := by
    obtain ⟨b, hb⟩ := h
    exact ⟨b, fun j hj ↦ (F.map_isZero (hb j hj)).of_iso (e V j)⟩
  have hl (V : CochainComplex (proEtaleRingModules X R) ℤ)
      (h : ∀ j, finiteLocal X A (V.homology j)) :
      ∀ j, SheafOfModules.IsLocallyConstantFiniteType J B ((W.obj V).homology j) := by
    intro j
    exact SheafOfModules.locallyConstantFiniteType_of_iso J B (e V j)
      ((finiteLocal_encoding X A _).mp (h j))
  obtain ⟨t⟩ := encoding_tensor X A
  have hkP := (kflat_equivalence F t P).mpr hp
  have hkQ := (kflat_equivalence F t Q).mpr hq
  have h := small_tensor J B (W.obj P) (W.obj Q) hkP hkQ
    (hb P hbP) (hb Q hbQ) (hl P hlP) (hl Q hlQ) i
  obtain ⟨q⟩ := ProEtale.tensorComplexTransportAux F t P Q
  apply (finiteLocal_encoding X A _).mpr
  exact SheafOfModules.locallyConstantFiniteType_of_iso J B
    ((e _ i).symm ≪≫ (HomologicalComplex.homologyFunctor _ _ i).mapIso q) h

/-- A bounded-above tensor is finite locally constant after restriction whenever
its input cohomology sheaves are finite locally constant there. Zero input cohomology
sheaves need no local-model hypothesis. The coefficient ring is any finite commutative
ring, and the restricting morphism is arbitrary. -/
theorem proEtale_restrictedTensor_finiteLocalConstancy
    {T X : Scheme.{u}} (a : X ⟶ T) (A : Type u) [CommRing A] [Finite A]
    (K L P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := proEtaleConstantRing T A) P)
    (hKb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      (((proEtaleConstantModulePullbackFunctor a A).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj K).homology j))
    (hLb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      (((proEtaleConstantModulePullbackFunctor a A).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj L).homology j))
    (hK : ∀ j : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
          (DerivedCategory.Q.obj K)) →
      IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback a A
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T A)) j).obj (DerivedCategory.Q.obj K))) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback a A ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
              (DerivedCategory.Q.obj K)))))
    (hL : ∀ j : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
          (DerivedCategory.Q.obj L)) →
      IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback a A
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T A)) j).obj (DerivedCategory.Q.obj L))) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback a A ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T A)) j).obj
              (DerivedCategory.Q.obj L)))))
    (i : ℤ) :
    IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback a A
      ((DerivedCategory.homologyFunctor (proEtaleRingModules T
        (proEtaleConstantRing T A)) i).obj (derivedTensor T A K L P f hf hP))) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
        (proEtaleConstantModulePullback a A ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj
            (derivedTensor T A K L P f hf hP)))) := by
  classical
  let RT := proEtaleConstantRing T A
  let RX := proEtaleConstantRing X A
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} RT
  let := SheafOfModules.symmetricCategory.{u, u + 1, u + 1} RT
  let := SheafOfModules.monoidalClosed_kfg.{u + 1, u} (R := RT)
  let := SheafOfModules.monoidalPreadditive_kfg.{u + 1, u} RT
  let := SheafOfModules.isGrothendieckAbelian_kfg.{u + 1, u} RT
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} RX
  let F := proEtaleConstantModulePullbackFunctor a A
  let W := F.mapHomologicalComplex (.up ℤ)
  have := hf
  obtain ⟨R, r, hr, hrf, hqr, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral P
  obtain ⟨S, s, hs, hsf, hqs, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
  have := hqr
  have := hqs
  have hR := pullback_kflat a A R hr hrf
  have hS := pullback_kflat a A S hs hsf
  have eR (j : ℤ) : (W.obj R).homology j ≅ (W.obj K).homology j :=
    asIso (HomologicalComplex.homologyMap (W.map (r ≫ f)) j)
  have eS (j : ℤ) : (W.obj S).homology j ≅ (W.obj L).homology j :=
    asIso (HomologicalComplex.homologyMap (W.map s) j)
  have hl (V : CochainComplex (proEtaleRingModules T RT) ℤ)
      (h : ∀ j, ¬ IsZero ((DerivedCategory.homologyFunctor _ j).obj
        (DerivedCategory.Q.obj V)) → finiteLocal X A
          (F.obj ((DerivedCategory.homologyFunctor _ j).obj (DerivedCategory.Q.obj V))))
      (j : ℤ) : finiteLocal X A ((W.obj V).homology j) := by
    let H := (DerivedCategory.homologyFunctor _ j).obj (DerivedCategory.Q.obj V)
    have hH : finiteLocal X A (F.obj H) := by
      by_cases hzero : IsZero H
      · exact finiteLocal_zero X A _ (F.map_isZero hzero)
      · exact h j hzero
    exact finiteLocal_iso X A (proEtaleConstantModulePullbackHomologyIso a A V j).symm hH
  have hbR : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((W.obj R).homology j) := by
    obtain ⟨b, hb⟩ := hKb
    exact ⟨b, fun j hj ↦ (hb j hj).of_iso (eR j)⟩
  have hbS : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((W.obj S).homology j) := by
    obtain ⟨b, hb⟩ := hLb
    exact ⟨b, fun j hj ↦ (hb j hj).of_iso (eS j)⟩
  have htotal := intrinsic_tensor X A (W.obj R) (W.obj S) hR hS hbR hbS
    (fun j ↦ finiteLocal_iso X A (eR j).symm (hl K hK j))
    (fun j ↦ finiteLocal_iso X A (eS j).symm (hl L hL j)) i
  have hpCat := kflat_of_acyclic P hP
  have hsCat := kflat_of_acyclic S hs
  have : QuasiIso (r ▷ S) :=
    (CochainComplex.kFlat_iff_preservesQuasiIso S).1 hsCat |>.2 r hqr
  have : QuasiIso (P ◁ s) :=
    (CochainComplex.kFlat_iff_preservesQuasiIso P).1 hpCat |>.1 s hqs
  let e : (R ⊗ S).homology i ≅ (P ⊗ L).homology i :=
    asIso (HomologicalComplex.homologyMap (r ▷ S) i) ≪≫
      asIso (HomologicalComplex.homologyMap (P ◁ s) i)
  have := constantComparison_isIso a A
  let c := asIso (proEtaleCoefficientInverseImageMap a A)
  let t := proEtaleTensorPullbackTotalIso a RT RX c R S
  let q : (CochainComplex.mapBifunctor (W.obj R) (W.obj S)
      (curriedTensor _)).homology i ≅ F.obj ((P ⊗ L).homology i) :=
    (HomologicalComplex.homologyFunctor _ _ i).mapIso t ≪≫
      ((R ⊗ S).sc i).mapHomologyIso F ≪≫ F.mapIso e
  have hout := finiteLocal_iso X A q htotal
  exact finiteLocal_iso X A
    (F.mapIso ((DerivedCategory.homologyFunctorFactors _ i).app (P ⊗ L)).symm) hout

end AlgebraicGeometry.Scheme

end Proof
