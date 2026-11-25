/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import all WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
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
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
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
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import all Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all Mathlib.Algebra.Category.Grp.Colimits
import all WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import all WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientGeneralPullbackIso

/-! # Ordinary rational coefficient composition and the normalized module and derived compositor.

## References

* Bhatt--Scholze, Remark 6.8.15, p. 62
* Stacks Tags 03CB, 0D6D, 07A4, 099N
* Stacks Tags 03CB, 03EL, 0D6D and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

private theorem ordinaryCoefficient_eq {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (hc : rationalCoefficientRestrictionNormalized l E f c) :
    c = rationalContinuousPullback l E f := by
  let := coefficientExtensionNormedField l E
  apply ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).injective
  apply Sheaf.hom_ext
  ext U s
  apply ContinuousMap.ext
  intro x
  exact (hc U.unop s x).trans
    (rationalContinuousPullback_normalized l E f U.unop s x).symm

private abbrev ordinaryRight {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) :=
  pbcRestrict c ⋙ proEtaleRingModuleDirectImage f (rationalCoefficientSheaf l T E)
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E)) (Iso.refl _)

private abbrev ordinaryAdj {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) :=
  (proEtaleRingModuleAdjunction f (rationalCoefficientSheaf l T E)
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E)) (Iso.refl _)).comp (pbcScalarAdjunction c)

private theorem ordinaryAdj_unit {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (M : pbcModules T (rationalCoefficientSheaf l T E))
    (V : T.ProEt) (m : M.val.obj (op V)) :
    ((ordinaryAdj l E f c).unit.app M).val.app (op V) m =
      pbcTensorSection c
        ((proEtaleRingModulePullback f (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
        (op ((proEtaleBaseChange f).obj V)) 1
        (proEtaleRingModuleUnitSection f (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m) := by
  change ((pbcScalarAdjunction c).unit.app _).val.app
      (op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingModuleAdjunction f (rationalCoefficientSheaf l T E)
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E)) (Iso.refl _)).unit.app M).val.app (op V) m) = _
  rw [canonicalAdjunction_normalized f (rationalCoefficientSheaf l T E)
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E)) (Iso.refl _)]
  exact (pbcScalarAdjunction_exists c).exists.choose_spec _ _ _

attribute [local irreducible] rationalCoefficientSheaf in
private def ordinaryRightIso {S T : Scheme.{u}} (f : S ⟶ T)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) [IsIso c] :
    ordinaryRight l E f c ≅ proEtaleRingModuleDirectImage f
      (rationalCoefficientSheaf l T E) (rationalCoefficientSheaf l S E) (asIso c) := by
  let R := rationalCoefficientSheaf l T E
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let ρ := proEtaleRingDirectImageMap f R (L.obj R) (Iso.refl _)
  have hh : ρ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map c =
      proEtaleRingDirectImageMap f R (rationalCoefficientSheaf l S E) (asIso c) := by
    dsimp only [ρ, proEtaleRingDirectImageMap, Iso.refl_hom, asIso_hom]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact SheafOfModules.pushforwardCongr (F := proEtaleBaseChange f)
    (J := ProEt.topology T) (K := ProEt.topology S)
    (R := (adicLisseForget S).obj (rationalCoefficientSheaf l S E))
    (S := (adicLisseForget T).obj R)
    (φ := (adicLisseForget T).map ρ ≫
      (proEtaleSheafDirectImage f RingCat.{u + 1}).map ((adicLisseForget S).map c))
    (congrArg ((adicLisseForget T).map) hh)

-- Nested chart conversions arise in the explicit tensor-section normalization.
attribute [local irreducible] rationalCoefficientSheaf in
/-- Ordinary rational coefficient composition and the normalized module and derived compositor. -/
theorem rationalOrdinaryPullbackComposition (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX) :
    let unitSection {S T : Scheme.{u}} (g : S ⟶ T)
        (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
        (M : pbcModules T (rationalCoefficientSheaf l T E))
        (V : T.ProEt) (m : M.val.obj (op V)) :
        ((rationalPullModule l E g c).obj M).val.obj
          (op ((proEtaleBaseChange g).obj V)) :=
      pbcTensorSection c
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)
    let scalarSection {S T : Scheme.{u}} (g : S ⟶ T)
        (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
        (V : T.ProEt) (e : (rationalCoefficientSheaf l T E).obj.obj (op V)) :
        (rationalCoefficientSheaf l S E).obj.obj (op ((proEtaleBaseChange g).obj V)) :=
      c.hom.app (op ((proEtaleBaseChange g).obj V))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
          (rationalCoefficientSheaf l T E)).hom.app (op V) e)
    let scalarMul (T : Scheme.{u})
        (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
        (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
      e • m
    (ac.rationalCoefficient =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l X E) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.rationalCoefficient ≫
      ah.rationalCoefficient) ∧
    ∃ (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
      rationalPullModule l E h ah.rationalCoefficient ≅
    rationalPullModule l E (h ≫ g) ac.rationalCoefficient),
    (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V))
      (e' : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange g).obj V)))
      (e'' : (rationalCoefficientSheaf l Z E).obj.obj
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
    (moduleComp.hom.app M).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (scalarMul Z
        ((rationalPullModule l E h ah.rationalCoefficient).obj
          ((rationalPullModule l E g ag.rationalCoefficient).obj M))
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) e''
        (unitSection h ah.rationalCoefficient
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          ((proEtaleBaseChange g).obj V)
          (scalarMul Y
            ((rationalPullModule l E g ag.rationalCoefficient).obj M)
            (op ((proEtaleBaseChange g).obj V)) e'
            (unitSection g ag.rationalCoefficient M V m)))) =
      scalarMul Z
        ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M)
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (e'' * scalarSection h ah.rationalCoefficient
          ((proEtaleBaseChange g).obj V) e')
        (((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.map
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
            (unitSection (h ≫ g) ac.rationalCoefficient M V m))) ∧
    ∃ (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
      rationalPullDerived l E h ah.rationalCoefficient ≅
    rationalPullDerived l E (h ≫ g) ac.rationalCoefficient),
    (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambientComp.hom.app (DerivedCategory.Q.obj P) ≫
        rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient P =
      (rationalPullDerived l E h ah.rationalCoefficient).map
          (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
        rationalPullComplexCounit l E h ah.rationalCoefficient
          (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex moduleComp (.up ℤ)).hom.app P)) := by
  classical
  dsimp only
  have hg := ordinaryCoefficient_eq l E g ag.rationalCoefficient ag.rational_normalization
  have hh := ordinaryCoefficient_eq l E h ah.rationalCoefficient ah.rational_normalization
  have hc := ordinaryCoefficient_eq l E (h ≫ g) ac.rationalCoefficient
    ac.rational_normalization
  have hcoeff : ac.rationalCoefficient =
      (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l X E) ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.rationalCoefficient ≫
        ah.rationalCoefficient := by
    rw [hg, hh, hc]
    let := coefficientExtensionNormedField l E
    with_unfolding_all
      exact continuousCoefficientPullback_comp (ULift.{u + 1, u} E) h g
  refine ⟨hcoeff, ?_⟩
  have : IsIso ag.rationalCoefficient := hg.symm ▸ inferInstance
  have : IsIso ah.rationalCoefficient := hh.symm ▸ inferInstance
  have : IsIso ac.rationalCoefficient := hc.symm ▸ inferInstance
  let R := rationalCoefficientSheaf l X E
  let S := rationalCoefficientSheaf l Y E
  let T := rationalCoefficientSheaf l Z E
  let cg := asIso ag.rationalCoefficient
  let ch := asIso ah.rationalCoefficient
  let cc := asIso ac.rationalCoefficient
  have hcc : cc = (proEtaleRingInverseImageComp h g).app R ≪≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso cg ≪≫ ch := by
    apply Iso.ext
    exact hcoeff
  obtain ⟨d₀, _, hd₀, _⟩ := proEtale_tensor_composition_unit h g R S T cg ch cc hcc
  let eg := ordinaryRightIso l E g ag.rationalCoefficient
  let eh := ordinaryRightIso l E h ah.rationalCoefficient
  let ec := ordinaryRightIso l E (h ≫ g) ac.rationalCoefficient
  let ei := isoWhiskerRight eh (ordinaryRight l E g ag.rationalCoefficient) ≪≫
    isoWhiskerLeft (proEtaleRingModuleDirectImage h S T ch) eg
  let d := ec ≪≫ d₀ ≪≫ ei.symm
  have hd (N : pbcModules Z T) (U : X.ProEt)
      (m : ((ordinaryRight l E (h ≫ g) ac.rationalCoefficient).obj N).val.obj (op U)) :
      (d.hom.app N).val.app (op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp h g).inv.app U).op m := by
    exact hd₀ N U m
  let adjg := ordinaryAdj l E g ag.rationalCoefficient
  let adjh := ordinaryAdj l E h ah.rationalCoefficient
  let adjc := ordinaryAdj l E (h ≫ g) ac.rationalCoefficient
  obtain ⟨moduleComp, hunit⟩ := mate_iso adjc (adjg.comp adjh) d
  refine ⟨moduleComp, ?_, ?_⟩
  · intro M V m e' e''
    have hu := congrArg (fun q ↦ q.val.app (op V) m) (hunit M)
    change (moduleComp.hom.app M).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        ((adjh.unit.app ((rationalPullModule l E g ag.rationalCoefficient).obj M)).val.app
          (op ((proEtaleBaseChange g).obj V)) ((adjg.unit.app M).val.app (op V) m)) =
      (d.hom.app _).val.app (op V) ((adjc.unit.app M).val.app (op V) m) at hu
    rw [hd] at hu
    simp only [← ordinaryAdj_unit]
    let U := (proEtaleBaseChange g).obj V
    let W := (proEtaleBaseChange h).obj U
    let N := (rationalPullModule l E h ah.rationalCoefficient).obj
      ((rationalPullModule l E g ag.rationalCoefficient).obj M)
    let u : ((rationalPullModule l E g ag.rationalCoefficient).obj M).val.obj (op U) :=
      (adjg.unit.app M).val.app (op V) m
    let v : N.val.obj (op W) :=
      (adjh.unit.app ((rationalPullModule l E g ag.rationalCoefficient).obj M)).val.app
        (op U) u
    let w : N.val.obj (op W) :=
      (adjh.unit.app ((rationalPullModule l E g ag.rationalCoefficient).obj M)).val.app
        (op U) (e' • u)
    let b : (rationalCoefficientSheaf l Z E).obj.obj (op W) :=
      ah.rationalCoefficient.hom.app (op W)
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app
          (rationalCoefficientSheaf l Y E)).hom.app (op U) e')
    let t : ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.obj
        (op W) :=
      ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.map
        ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          ((adjc.unit.app M).val.app (op V) m)
    let φ := ((moduleComp.hom.app M).val.app (op W)).hom
    have hs : w = b • v := by
      exact ((adjh.unit.app
        ((rationalPullModule l E g ag.rationalCoefficient).obj M)).val.app
          (op U)).hom.map_smul e' u
    have hv : φ v = t := hu
    change φ (e'' • w) = (e'' * b) • t
    rw [hs, φ.map_smul, φ.map_smul, hv, ← mul_smul]
  · let factors {S T : Scheme.{u}} (f : S ⟶ T)
        (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) [IsIso c] :
        DerivedCategory.Q ⋙ rationalPullDerived l E f c ≅
          (rationalPullModule l E f c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
      have hExact := rationalPullExtendExact c
      let := hExact.1
      let := hExact.2
      exact isoWhiskerRight (proEtaleRingDerivedPullbackFactors f
          (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _)) (pbcDerivedExtend c) ≪≫
        isoWhiskerLeft ((proEtaleRingModulePullback f (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _)).mapHomologicalComplex (.up ℤ))
          (rationalPullScalarFactors c)
    have hfactors {S T : Scheme.{u}} (f : S ⟶ T)
        (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) [IsIso c]
        (P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ) :
        (factors f c).hom.app P = rationalPullComplexCounit l E f c P := by
      rfl
    let a := isoWhiskerRight (factors g ag.rationalCoefficient)
        (rationalPullDerived l E h ah.rationalCoefficient) ≪≫
      isoWhiskerLeft ((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
        (.up ℤ)) (factors h ah.rationalCoefficient)
    let b := factors (h ≫ g) ac.rationalCoefficient
    obtain ⟨ambientComp, hambient⟩ := rationalPullDescendIso
      (rationalPullDerived l E g ag.rationalCoefficient ⋙
        rationalPullDerived l E h ah.rationalCoefficient)
      (rationalPullDerived l E (h ≫ g) ac.rationalCoefficient) _ _ a b
      (isoWhiskerRight (NatIso.mapHomologicalComplex moduleComp (.up ℤ)) DerivedCategory.Q)
    refine ⟨ambientComp, fun P ↦ ?_⟩
    simpa only [a, b, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      whiskerRight_app, whiskerLeft_app, hfactors, Category.assoc] using hambient P

end AlgebraicGeometry.Scheme
