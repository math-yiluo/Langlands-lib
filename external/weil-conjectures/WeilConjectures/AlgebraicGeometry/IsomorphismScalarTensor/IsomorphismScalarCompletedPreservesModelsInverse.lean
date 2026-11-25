/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModelBase
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Homology.RingedSiteKFlatStalkCriterion
import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
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
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.RingedSitePointUniversalTensor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.PUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Homology.RingedSitePointExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.RingedSitePointFinitePresentationRetract
import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.Sites.InverseImageFreeModule
import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Finsupp.Pi
import WeilConjectures.Algebra.Homology.RingedSitePointKFlatResolution
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.RingedSitePointAcyclic
import WeilConjectures.Algebra.Homology.UniversalAcyclicModuleKFlat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.Sites.FinitarySliceEnoughPoints
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.FinitarySiteEnoughPoints
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.CategoryTheory.Sites.PointSystemSaturation
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.PointSystemRefineAll
import WeilConjectures.CategoryTheory.PointSystemRefinementMap
import WeilConjectures.AlgebraicGeometry.PointSystemRefine
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.PointSystemRefinementChainExists
import WeilConjectures.CategoryTheory.PointSystemChain
import Mathlib.Order.Directed
import WeilConjectures.CategoryTheory.PointSystemExtensions
import WeilConjectures.CategoryTheory.PointSystemDiagram
import Mathlib.Order.Category.PartOrdEmb
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Order.Hom.Set
import WeilConjectures.CategoryTheory.PointSystemPosetalRefine
import WeilConjectures.CategoryTheory.PointSystemPosetalReplacement
import Mathlib.Order.Antisymmetrization
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.PointSystemSchedule
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.CategoryTheory.Filtered.Grothendieck
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Sites.PointFamilyConservative
import WeilConjectures.TraceFormula.InverseSystemSitePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! Inverse-image preservation of good completed integral models.

This is the inverse-image part of `scalar_completed_preserves_models`.

## Implementation details

The independent site and coefficient universes require a ringed-topos K-flat pullback argument
for the sectionwise inverse-image model.

## References

* Stacks Project, Modules on Sites, Tag 03D2
* Cohomology on Sites, Tag 0DEP
* Stacks Project, Tags 0DEN, 0DEP, 08FC and 09A5
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

attribute [local instance 2000] SheafOfModules.hasSheafify_coefficientUniverse
attribute [local instance 2000] SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

private theorem postcompose_cocontinuous
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleIsoPostcompose g).IsCocontinuous (ProEt.topology X) (ProEt.topology Y) := by
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt := CategoryTheory.Equivalence.mk
    (proEtaleIsoPostcompose g) (proEtaleIsoPostcompose (inv g))
    e.2.1.some.symm e.2.2.1.some
  exact (E.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 e.2.2.2.2.some

/-- Sectionwise inverse image with an invertible coefficient identification preserves
flat module sheaves. -/
private theorem sectionwise_preservesFlat
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{max u (t + 1)} X.ProEt] [EssentiallySmall.{max u (t + 1)} Y.ProEt]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})
    (c : (isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj RY ≅ RX)
    (F : SheafOfModules.{max u (t + 1)} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY) ⥤
      SheafOfModules.{max u (t + 1)} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RX)) [F.Additive]
    (_hF : F = isoSectionwiseModuleInverseImage.{t, u} g
      (RY := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY)
      (RX := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RX)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso c).hom) :
    ∀ M : SheafOfModules.{max u (t + 1)} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY),
      SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := ProEt.topology Y) (R := RY) M →
        SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
          (J := ProEt.topology X) (R := RX) (F.obj M) := by
  subst F
  intro M hM
  simp only [isoSectionwiseModuleInverseImage, IsIso.Iso.inv_hom]
  let G := proEtaleIsoPostcompose g
  have : G.IsCocontinuous (ProEt.topology X) (ProEt.topology Y) :=
    postcompose_cocontinuous g
  have hc (V : X.ProEt) (b : RY.obj.obj (op (G.obj V))) :
      c.inv.hom.app (op V) (c.hom.hom.app (op V) b) = b := by
    have h := congrArg (fun k ↦ k.hom.app (op V) b) c.hom_inv_id
    exact h
  have hd (V : X.ProEt) (a : RX.obj.obj (op V)) :
      c.hom.hom.app (op V) (c.inv.hom.app (op V) a) = a := by
    have h := congrArg (fun k ↦ k.hom.app (op V) a) c.inv_hom_id
    exact h
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{t + 1, t,
    max u (t + 1), max u (t + 1)} RX
  intro U n a s hs
  change Fin n → M.val.obj (op (G.obj U)) at s
  change (∑ p, c.inv.hom.app (op U) (a p) • s p) = 0 at hs
  obtain ⟨S, hS, hlocal⟩ :=
    (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{t + 1, t,
        max u (t + 1), max u (t + 1)}
      RY M).1 hM
      (G.obj U) n (fun p ↦ c.inv.hom.app (op U) (a p)) s hs
  refine ⟨S.functorPullback G, G.cover_lift _ _ hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, t, hfac, hrel⟩ := hlocal (G.obj V) (G.map f) hf
  refine ⟨l, fun p q ↦ c.hom.hom.app (op V) (b p q), t, ?_, ?_⟩
  · intro p
    change M.val.map (G.map f).op (s p) =
      ∑ q, c.inv.hom.app (op V) (c.hom.hom.app (op V) (b p q)) • t q
    simpa only [hc] using hfac p
  · intro q
    have h := congrArg (c.hom.hom.app (op V)) (hrel q)
    simp only [map_sum, map_mul, map_zero] at h
    have hn (p : Fin n) :
        c.hom.hom.app (op V)
            (RY.obj.map (G.map f).op (c.inv.hom.app (op U) (a p))) =
          RX.obj.map f.op (a p) := by
      have hnat := ConcreteCategory.congr_hom (c.hom.hom.naturality f.op)
        (c.inv.hom.app (op U) (a p))
      change _ = RX.obj.map f.op
        (c.hom.hom.app (op U) (c.inv.hom.app (op U) (a p))) at hnat
      rw [hd] at hnat
      exact hnat
    simpa only [hn] using h

/-- The explicit algebraic presentation of sectionwise inverse image.
The ring identification is induced by `c`, and the underlying module identification
is the identity. The scalar graph follows by cancelling `c` with its inverse. -/
private noncomputable def sectionwiseAlgebraicLift
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{max u (t + 1)} X.ProEt] [EssentiallySmall.{max u (t + 1)} Y.ProEt]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})
    (c : (isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj RY ≅ RX) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{t + 1, t, t + 1, t,
      max u (t + 1), max u (t + 1)}
      (isoSectionwiseInverseImage g (Type (max u (t + 1)))) RY RX := by
  let U := CategoryTheory.forget CommRingCat.{max u (t + 1)} ⋙
    uliftFunctor.{max u (t + 1), max u (t + 1)}
  let er := (sheafCompose (ProEt.topology X) U).mapIso c
  refine
    { ringUnderlying := er
      modules := isoSectionwiseModuleInverseImage.{t, u} g
        (RY := (sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY)
        (RX := (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RX)
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso c).hom
      moduleUnderlying := Iso.refl _
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (t.hom.app _ x).down =
      (c.hom.hom.app V).hom (a.hom.app _ x).down +
        (c.hom.hom.app V).hom (b.hom.app _ x).down
    simpa only [id, map_add] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro T a b t h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (t.hom.app _ x).down =
      (c.hom.hom.app V).hom (a.hom.app _ x).down *
        (c.hom.hom.app V).hom (b.hom.app _ x).down
    simpa only [id, map_mul] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro T a h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (a.hom.app _ x).down = 0
    simpa only [id, map_zero] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro T a h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (a.hom.app _ x).down = 1
    simpa only [id, map_one] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro M T a b t h V x
    exact h _ x
  · intro M T a h V x
    exact h _ x
  · intro M T a b t h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (t.hom.app _ x).down =
      ((inv ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso c).hom).hom.app V).hom
          ((c.hom.hom.app V).hom (a.hom.app _ x).down) •
            (show M.val.obj ((proEtaleIsoPostcompose g).op.obj V) from
              (b.hom.app _ x).down)
    rw [IsIso.Iso.inv_hom]
    change (t.hom.app _ x).down =
      (c.inv.hom.app V).hom ((c.hom.hom.app V).hom (a.hom.app _ x).down) •
        (show M.val.obj ((proEtaleIsoPostcompose g).op.obj V) from
          (b.hom.app _ x).down)
    have hc (z : RY.obj.obj ((proEtaleIsoPostcompose g).op.obj V)) :
        (c.inv.hom.app V).hom ((c.hom.hom.app V).hom z) = z :=
      congrArg (fun f ↦ (f.hom.app V).hom z) c.hom_inv_id
    rw [hc]
    exact h _ x

/-- Sectionwise inverse image with an invertible coefficient identification preserves
K-flat complexes for the independent-coefficient tensor predicate. -/
private theorem sectionwise_preservesKFlat
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{max u (t + 1)} X.ProEt] [EssentiallySmall.{max u (t + 1)} Y.ProEt]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})
    (c : (isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj RY ≅ RX)
    (F : SheafOfModules.{max u (t + 1)} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY) ⥤
      SheafOfModules.{max u (t + 1)} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RX)) [F.Additive]
    (_hF : F = isoSectionwiseModuleInverseImage.{t, u} g
      (RY := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY)
      (RX := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RX)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).mapIso c).hom) :
    ∀ K : CochainComplex (SheafOfModules.{max u (t + 1)} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj RY)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
        (J := ProEt.topology Y) (R := RY) K →
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
          (J := ProEt.topology X) (R := RX)
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  -- Use the already implemented stalk argument of Stacks 0DEP instead of
  -- reconstructing the total-tensor comparison for this particular equivalence.
  classical
  subst F
  let L := isoSectionwiseInverseImage g (Type (max u (t + 1)))
  have : L.IsEquivalence :=
    (isoSectionwiseInverseImage_equivalence.{t, (max u (t + 1)) + 1, max u (t + 1), 0, 0}
      g (Type (max u (t + 1)))).1
  let f : GeometricMorphism
      (Sheaf (ProEt.topology X) (Type (max u (t + 1))))
      (Sheaf (ProEt.topology Y) (Type (max u (t + 1)))) :=
    { inverse := L
      direct := L.asEquivalence.inverse
      adj := L.asEquivalence.toAdjunction
      leftExact := inferInstance }
  let I := sectionwiseAlgebraicLift g RY RX c
  have : I.modules.Additive := by
    dsimp only [I, sectionwiseAlgebraicLift]
    infer_instance
  obtain ⟨ι, p, hp⟩ := AlgebraicGeometry.proEtale_enoughPoints.{t, u} X
  let s : ∀ i, RingedSitePoint RX (p i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty RX (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro A B a _
    exact hp a (fun i ↦ (isIso_iff_bijective ((p i).inverse.map a)).1 inferInstance)
  exact SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (ProEt.topology Y) (ProEt.topology X) f I ι p s hcons

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The sectionwise inverse image sends every good representative to a good one. -/
theorem inverseImageIntegralModules_preserves_good
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    integralOperationsGoodComplex l E X
      ((inverseComplex l E g).obj P.obj) := by
  classical
  let RY := completedIntegralCommRingSheafUnrestricted l E Y
  let RX := completedIntegralCommRingSheafUnrestricted l E X
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let c : (isoSectionwiseInverseImage g CommRingCat).obj RY ≅ RX :=
    W.preimageIso (asIso (inverseImageCompletedCoefficientMap l E g))
  have hc : W.map c.hom = inverseImageCompletedCoefficientMap l E g :=
    W.map_preimage _
  have hF : inverseImageIntegralModules l E g =
      isoSectionwiseModuleInverseImage g (W.mapIso c).hom := by
    simp only [inverseImageIntegralModules, isoSectionwiseModuleInverseImage, ← hc]
    rfl
  rcases P.property with ⟨hk, hflat⟩
  constructor
  · exact sectionwise_preservesKFlat g RY RX c (inverseImageIntegralModules l E g)
      hF P.obj hk
  · intro i
    exact sectionwise_preservesFlat g RY RX c (inverseImageIntegralModules l E g)
      hF (P.obj.X i) (hflat i)

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
