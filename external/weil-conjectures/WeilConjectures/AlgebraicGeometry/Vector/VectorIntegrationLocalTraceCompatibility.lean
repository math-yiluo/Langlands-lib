/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.CategoryTheory.Etale.EtaleDegreeZeroHom
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
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
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
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
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDegreeZeroHomRestriction
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapChartPrefix
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTowerCounitBaseChange

/-! # Compatibility of vector-bundle local traces on overlaps

Source: blueprint sec-smooth-purity/sk-prop-an/def-amb-vector-integration,
overlap calculation and normalization paragraph.
(blueprint: lem-amb-vector-integration-local-trace-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor upperStar

-- The constant unit and the Hom correspondence use the same degree-zero embedding.
attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor

private theorem four_assoc {C : Type*} [Category C] {W X Y Z R : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ R) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem map_comp_tail {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {X Y Z : C} {K R : D}
    (a : K ⟶ P.obj X) (f : X ⟶ Y) (g : Y ⟶ Z) (b : P.obj Z ⟶ R) :
    a ≫ P.map f ≫ P.map g ≫ b = a ≫ P.map (f ≫ g) ≫ b := by
  rw [P.map_comp]
  simp only [Category.assoc]

private theorem map_iso_cancel {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {X Y Z : C} {K R : D}
    (a : K ⟶ P.obj X) (f : X ⟶ Y) (β : Z ≅ Y) (b : P.obj Y ⟶ R) :
    a ≫ P.map (f ≫ β.inv) ≫ P.map β.hom ≫ b = a ≫ P.map f ≫ b := by
  rw [← P.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem restricted_normalization (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    [Etale p] [Etale v] [Etale w] (hw : w = p ≫ v)
    {K : DerivedCategoryModule A S}
    {M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M)
    (τ : (ordinaryFinitePullback A v).obj K ⟶ ordinaryFiniteUnit A U) :
    (etaleDegreeZeroHomEquiv A w α).symm
        (compRestriction v p w hw
          (etaleDegreeZeroHomEquiv A v α (τ ≫ (ordinaryFiniteUnitPullback A v).inv))) ≫
        (ordinaryFiniteUnitPullback A w).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app K ≫
        (ordinaryFinitePullback A p).map τ ≫ (ordinaryFiniteUnitPullback A p).hom := by
  rw [etaleDegreeZeroHomEquiv_symm_compRestriction, Equiv.symm_apply_apply]
  rw [← ordinaryFiniteUnitPullback_comp A p v w hw]
  simp only [(ordinaryFinitePullback A p).map_comp, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    map_iso_cancel (ordinaryFinitePullback A p)
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app K) τ
      (ordinaryFiniteUnitPullback A v) (ordinaryFiniteUnitPullback A p).hom

private theorem tower_unit_counit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (hD : OrdinaryFiniteP1BaseChange A N hA t D)
    {T U : Scheme.{u}} [IsNoetherian T] [IsNoetherian U]
    (p : T ⟶ U) (hU : IsUnit (N : Γ(U, ⊤))) (d : ℕ) :
    affineTraceUnitBaseChange A N hA t p hU d ≫
        affineTraceCounit A N hA t D T (affineTracePullbackInvertible N p hU) d =
      (ordinaryFinitePullback A p).map (affineTraceCounit A N hA t D U hU d) ≫
        (ordinaryFiniteUnitPullback A p).hom := by
  have hn := (affineTraceAdjunction A N hA t D T
    (affineTracePullbackInvertible N p hU) d).counit.naturality
      (ordinaryFiniteUnitPullback A p).hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  unfold affineTraceUnitBaseChange affineTraceCounit
  simp only [Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (ordinaryFiniteUnitPullback A p).hom)
    (affineTraceTowerCounit_baseChange A N hN hA t D hD p hU d (ordinaryFiniteUnit A U))

private theorem chart_trace_eq_prefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) [IsNoetherian V.toScheme]
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    vectorIntegrationLocalTrace N hN A hA t D S hS d F V e =
      vectorIntegrationChartPrefix N hN A hA t S hS d F V e ≫
        affineTraceCounit A N hA t D V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d := by
  unfold vectorIntegrationLocalTrace vectorIntegrationChartPrefix
  exact four_assoc _ _ _ _

private theorem overlap_prefix_counit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (hD : OrdinaryFiniteP1BaseChange A N hA t D)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (U V : S.Opens) [IsNoetherian U.toScheme] (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    vectorIntegrationOverlapPrefix N hN A hA t S hS d F U V hUV e ≫
        affineTraceCounit A N hA t D U.toScheme (affineTracePullbackInvertible N U.ι hS) d =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (S.homOfLE hUV) V.ι U.ι
        (S.homOfLE_ι hUV).symm).hom.app (vectorIntegrationSource A N hA S d F) ≫
        (ordinaryFinitePullback A (S.homOfLE hUV)).map
          (vectorIntegrationLocalTrace N hN A hA t D S hS d F V e) ≫
        (ordinaryFiniteUnitPullback A (S.homOfLE hUV)).hom := by
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  unfold vectorIntegrationOverlapPrefix
  simp only [Category.assoc]
  rw [tower_unit_counit N hN A hA t D hD]
  rw [chart_trace_eq_prefix N hN A hA t D S hS d F V e]
  exact map_comp_tail (ordinaryFinitePullback A (S.homOfLE hUV)) _
    (vectorIntegrationChartPrefix N hN A hA t S hS d F V e)
    (affineTraceCounit A N hA t D V.toScheme (affineTracePullbackInvertible N V.ι hS) d)
    (ordinaryFiniteUnitPullback A (S.homOfLE hUV)).hom

/-- The sheaf map corresponding to the prescribed derived trace on a frame open.
The identification of the source with a single sheaf is supplied explicitly; it is
not chosen by this definition. The local Hom correspondence has unique preimages.
Source: blueprint vector integration, degree-zero gluing paragraph.
(blueprint: lem-amb-vector-integration-local-trace-compatibility). -/
@[irreducible]
def vectorIntegrationLocalSheafTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).obj L ⟶
      (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).obj
        (ordinaryFiniteConstant A S) :=
  etaleDegreeZeroHomEquiv A V.ι α
    (vectorIntegrationLocalTrace N hN A hA t D S hS d F V e ≫
      (ordinaryFiniteUnitPullback A V.ι).inv)

/-- The local sheaf trace has exactly the prescribed derived normalization.
Source: blueprint vector integration, degree-zero gluing.
(blueprint: lem-amb-vector-integration-local-trace-compatibility). -/
theorem vectorIntegrationLocalSheafTrace_normalization_iff (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (ell : L ⟶ ordinaryFiniteConstant A S)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A V.ι).map
        (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) ≫
          (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS d F V e ↔
    (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).map ell =
      vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e := by
  unfold vectorIntegrationLocalSheafTrace
  exact etaleDegreeZeroHomEquiv_unit_normalization A V.ι α ell
    (vectorIntegrationLocalTrace N hN A hA t D S hS d F V e)

/-- On an étale object with lifts to two frame opens, the two traces from a fixed
normalized projective-line family with its base-change equations agree.
Source: blueprint vector integration, overlap calculation.
(blueprint: lem-amb-vector-integration-local-trace-compatibility).

Proof:
1. Restrict the frames to their intersection. Open inverse image is exact, so the
   degree-zero Hom correspondence commutes with restriction. Pasting of the actual
   compact-support exchanges and the normalized Tate composition equations express
   each restricted map as the prescribed affine counit for its restricted frame.
   The supplied base-change equation for the projective-line family passes to the
   ordered affine counit by composition of adjunctions.
2. Write the change of frames as e_j=e_i G. Their coordinate change is G transpose;
   consequently phi_i phi_j inverse is the substitution g=(G transpose) inverse.
   The inverse-coordinate squares paste to give B_j=rho_g B_i, with rho_g exactly
   affineLinearTraceAction. The intersection is Noetherian and N remains invertible.
3. Apply affineSpaceLinearTraceInvariance there: rho_g followed by the affine counit
   is that counit. Pull this equality back to the given étale object and evaluate
   its terminal section. Full faithfulness of singleFunctor gives equality of the
   sheaf maps, hence of the displayed descent components. The inserted alpha cancels
   on both sides. Rank zero and the empty intersection satisfy the same equations.
The separate uniqueness lemmas prove the base-change hypothesis from normalization,
and identify every other normalized family with the one used here. -/
theorem vectorIntegrationLocalSheafTrace_compatible_of_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (hD : OrdinaryFiniteP1BaseChange A N hA t D)
    (V V' : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (e' : VectorBundleZeroSection.Trivialization S d F V')
    (W : S.Etale) (q : W ⟶ Scheme.Etale.mk V.ι) (q' : W ⟶ Scheme.Etale.mk V'.ι) :
    descentComponent V.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e) q =
      descentComponent V'.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V' e') q' := by
  let U : S.Opens := V ⊓ V'
  let p : U.toScheme ⟶ V.toScheme := S.homOfLE inf_le_left
  let p' : U.toScheme ⟶ V'.toScheme := S.homOfLE inf_le_right
  have hp : U.ι = p ≫ V.ι := (S.homOfLE_ι inf_le_left).symm
  have hp' : U.ι = p' ≫ V'.ι := (S.homOfLE_ι inf_le_right).symm
  let : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian U.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  obtain ⟨g, hg⟩ := vectorIntegration_overlap_chart_prefix N hN A hA t S hS d F
    U V V' inf_le_left inf_le_right e e'
  obtain ⟨sq, hi⟩ := affineSpaceLinearTraceInvariance N hN A hA t D U.toScheme
    (affineTracePullbackInvertible N U.ι hS) d g
  have heq : sq = affineTraceLinearMap_isPullback U.toScheme d g := Subsingleton.elim _ _
  subst sq
  have hψ :
      compRestriction V.ι p U.ι hp
          (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e) =
        compRestriction V'.ι p' U.ι hp'
          (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V' e') := by
    apply (etaleDegreeZeroHomEquiv A U.ι α).symm.injective
    apply (cancel_mono (ordinaryFiniteUnitPullback A U.ι).hom).mp
    simp only [vectorIntegrationLocalSheafTrace]
    rw [restricted_normalization A p V.ι U.ι hp α,
      restricted_normalization A p' V'.ι U.ι hp' α]
    rw [← overlap_prefix_counit N hN A hA t D hD S hS d F U V inf_le_left e,
      ← overlap_prefix_counit N hN A hA t D hD S hS d F U V' inf_le_right e']
    rw [hg, Category.assoc, hi]
  let square := isPullback_opens_inf V V'
  have hq : q.left ≫ V.ι = W.hom := MorphismProperty.Over.w q
  have hq' : q'.left ≫ V'.ι = W.hom := MorphismProperty.Over.w q'
  let a : W.left ⟶ U.toScheme := square.lift q.left q'.left (hq.trans hq'.symm)
  have ha : a ≫ p = q.left := square.lift_fst _ _ _
  have ha' : a ≫ p' = q'.left := square.lift_snd _ _ _
  have haw : a ≫ U.ι = W.hom := by
    rw [hp, ← Category.assoc, ha]
    exact hq
  have : Etale (a ≫ U.ι) := by rw [haw]; exact W.prop
  have : Etale a := Etale.of_comp a U.ι
  rw [descentComponent_eq_compRestriction V.ι p U.ι hp _ q a ha haw,
    descentComponent_eq_compRestriction V'.ι p' U.ι hp' _ q' a ha' haw, hψ]

/-- The overlap equality also holds for separately supplied normalized Tate transports,
since the normalization determines both the Tate transport and the projective-line data.
Source: blueprint vector integration, overlap and canonical coefficient identifications.
(blueprint: lem-amb-vector-integration-local-trace-compatibility). -/
theorem vectorIntegrationLocalSheafTrace_compatible (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (t t' : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (D' : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t' T hT)
    (V V' : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (e' : VectorBundleZeroSection.Trivialization S d F V')
    (W : S.Etale) (q : W ⟶ Scheme.Etale.mk V.ι) (q' : W ⟶ Scheme.Etale.mk V'.ι) :
    descentComponent V.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e) q =
      descentComponent V'.ι
        (vectorIntegrationLocalSheafTrace N hN A hA t' D' S hS d F α V' e') q' := by
  have ht : t' = t := ordinaryFiniteTwistTransport_unique A N hA t' t
  subst t'
  have hd : D' = D := by
    funext T inst hT
    exact ordinaryFiniteP1Datum_unique A N hA t T hT (D' T hT) (D T hT)
  subst D'
  exact vectorIntegrationLocalSheafTrace_compatible_of_baseChange N hN A hA
    S hS d F α t D (ordinaryFiniteP1BaseChange_of_normalization N hN A hA t D)
    V V' e e' W q q'

end AlgebraicGeometry.Etale
