/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Compactification.NagataCompactification

public import Mathlib.Algebra.Homology.Single

import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-! # Vector-bundle integration charts and local trace maps

Source: blueprint sec-smooth-purity/sk-prop-an, order 1972.
(blueprint: proposition-purity-vector-bundles).

These are the existing coefficient, chart and normalization constructions. Cohomology
concentration follows by exact inverse image and the affine-space trace on a frame cover.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor ZeroObject
namespace AlgebraicGeometry.Etale

/-- Reuse concrete sheafification on each Zariski slice when elaborating finite-rank
module frames. This packages the existing Mathlib instance without a new assumption.
Source: blueprint order 1972, module frames (blueprint: proposition-purity-vector-bundles). -/
instance vectorIntegrationZariskiWeakSheafify (S : Scheme.{u}) :
    ∀ V : S.Opens, HasWeakSheafify
      ((Opens.grothendieckTopology S).over V) AddCommGrpCat.{u} :=
  fun V ↦ sheafToPresheaf_isRightAdjoint ((Opens.grothendieckTopology S).over V)
    AddCommGrpCat.{u}

/-- Reuse the existing local-bijection characterization of sheafification on each slice.
Source: blueprint order 1972, module frames (blueprint: proposition-purity-vector-bundles). -/
instance vectorIntegrationZariskiLocallyBijective (S : Scheme.{u}) :
    ∀ V : S.Opens,
      ((Opens.grothendieckTopology S).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  fun V ↦
    let J := (Opens.grothendieckTopology S).over V
    letI : ∀ P : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallyInjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallyInjective_toSheafify' J P
    letI : ∀ P : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallySurjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallySurjective_toSheafify' J P
    GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrpCat.{u}

/-- The geometric properties needed to form the ordinary compact support of the bundle.
Source: blueprint order 1972, first paragraph (blueprint: proposition-purity-vector-bundles).
Proof: the relative spectrum is affine, hence quasi-compact and separated by
lem-weil-pbc-affine-morphism-permanence. On an affine trivializing open its coordinate
ring is the polynomial algebra on d generators. The pointwise finite-type criterion
lem-weil-pbc-lft-pointwise-criterion gives local finite type. Finite type over the
Noetherian base gives a Noetherian total space by lem-weil-pbc-finite-type-over-noetherian.
-/
theorem vectorIntegration_geometry (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    IsAffineHom (VectorBundleZeroSection.π S d F) ∧
      LocallyOfFiniteType (VectorBundleZeroSection.π S d F) ∧
      IsNoetherian (VectorBundleZeroSection.scheme S d F) := by
  let : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (VectorBundleZeroSection.over S d F).property
  have hft : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) := by
    obtain ⟨I, U, hU, e⟩ :=
      Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
    apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFiniteType) U hU
    intro i
    let E := (e i).some
    let := (VectorBundleZeroSection.trivializationMap_spec S d F (U i) E).1
    rw [← (VectorBundleZeroSection.trivializationMap_spec S d F (U i) E).2.1]
    infer_instance
  let := hft
  let := LocallyOfFiniteType.isLocallyNoetherian (VectorBundleZeroSection.π S d F)
  let := QuasiCompact.compactSpace_of_compactSpace (VectorBundleZeroSection.π S d F)
  exact ⟨inferInstance, hft, ⟨⟩⟩

/-- Canonical inverse image of the ordered shifted Tate tensor: recurse using tensor
pullback, the normalized finite-line comparison, and the constant-unit comparison.
Source: blueprint order 1972, Tate identifications (blueprint: proposition-purity-vector-bundles).
-/
def vectorIntegrationBaseCoefficientPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y d) ≅
      affineLinearBaseCoefficient A N hA X d :=
  Nat.rec (motive := fun e ↦
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y e) ≅
      affineLinearBaseCoefficient A N hA X e)
    (ordinaryFiniteUnitPullback A f)
    (fun e r ↦ ordinaryFiniteTensorPullback A f (affineLinearBaseCoefficient A N hA Y e)
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≪≫
      ordinaryFiniteTensorRightMapIso A X r
        (ordinaryFiniteShiftedLinePullback A N hA t f hY)) d

/-- A_E(d)[2d], written as inverse image of the existing ordered shifted Tate tensor.
Each of the d factors is the concrete finite roots-of-unity Tate line shifted by two;
the zero-fold tensor is the constant complex. This uses no additional twist definition.
Source: blueprint order 1972, C_pi (blueprint: proposition-purity-vector-bundles). -/
def vectorIntegrationCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A (VectorBundleZeroSection.scheme S d F) :=
  (ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj
    (affineLinearBaseCoefficient A N hA S d)

/-- C_pi = R pi_! A_E(d)[2d], using the canonical chosen compactification. Nagata applies
because the bundle is separated and finite type and the Noetherian base is qcqs.
Source: blueprint order 1972, C_pi (blueprint: proposition-purity-vector-bundles). -/
def vectorIntegrationSource (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A S :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d F)).obj
    (vectorIntegrationCoefficient A N hA S d F)

/-- L_pi is the degree-zero cohomology sheaf of C_pi.
Source: blueprint order 1972, L_pi (blueprint: proposition-purity-vector-bundles). -/
def vectorIntegrationSheaf (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).obj (vectorIntegrationSource A N hA S d F)

/-- The inverse frame from the coordinate-tower affine space to the restricted bundle,
followed by the actual open inclusion into E. No coordinate isomorphism is chosen.
Source: blueprint order 1972, inverse-coordinate square
(blueprint: proposition-purity-vector-bundles). -/
def vectorIntegrationChart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    affineTraceTower V.toScheme d ⟶ VectorBundleZeroSection.scheme S d F :=
  letI := (VectorBundleZeroSection.trivializationMap_spec S d F V e).1
  (affineTraceAffineSpaceIso V.toScheme d).hom ≫
    inv (VectorBundleZeroSection.trivializationMap S d F V e) ≫
      ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V).ι

/-- The inverse-frame square over V → S is Cartesian.
Source: blueprint order 1972, inverse-coordinate square
(blueprint: proposition-purity-vector-bundles).
Proof: the open inverse-image square is Cartesian. The frame's concrete coordinate map
is an isomorphism over V by proposition-purity-vector-bundles; the coordinate tower is
the same affine space. Paste this isomorphism square with the open inverse-image square.
-/
theorem vectorIntegrationChart_isPullback (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    IsPullback (vectorIntegrationChart S d F V e) (affineTraceProjection V.toScheme d)
      (VectorBundleZeroSection.π S d F) V.ι := by
  let := (VectorBundleZeroSection.trivializationMap_spec S d F V e).1
  have hw :
      ((affineTraceAffineSpaceIso V.toScheme d).hom ≫
        inv (VectorBundleZeroSection.trivializationMap S d F V e)) ≫
          ((VectorBundleZeroSection.π S d F) ∣_ V) =
        affineTraceProjection V.toScheme d := by
    rw [← (VectorBundleZeroSection.trivializationMap_spec S d F V e).2.1]
    simp [affineTraceAffineSpaceIso, affineTraceToAffineSpace]
  have hi := IsPullback.of_horiz_isIso
    (fst := (affineTraceAffineSpaceIso V.toScheme d).hom ≫
      inv (VectorBundleZeroSection.trivializationMap S d F V e))
    (g := 𝟙 V.toScheme) (CommSq.mk (by simpa using hw))
  simpa only [vectorIntegrationChart, Category.id_comp, Category.assoc] using
    hi.paste_horiz (isPullback_morphismRestrict (VectorBundleZeroSection.π S d F) V).flip

/-- Canonical coefficient identification in the inverse-frame square. The equality of
its two composites is used between the inverse-image composition comparisons; then the
base Tate tensor is pulled back and the existing affine coefficient descent is inverted.
Source: blueprint order 1972, a_i (blueprint: proposition-purity-vector-bundles). -/
def vectorIntegrationChartCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A (vectorIntegrationChart S d F V e)).obj
        (vectorIntegrationCoefficient A N hA S d F) ≅
      (affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (vectorIntegrationChart S d F V e) (VectorBundleZeroSection.π S d F)).symm.app _ ≪≫
  (eqToIso (congrArg (ordinaryFinitePullback A)
    (vectorIntegrationChart_isPullback S d F V e).w)).app _ ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (affineTraceProjection V.toScheme d) V.ι).app _ ≪≫
  (ordinaryFinitePullback A (affineTraceProjection V.toScheme d)).mapIso
    (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) ≪≫
  (affineLinearCoefficientDescent A N hA t V.toScheme
    (affineTracePullbackInvertible N V.ι hS) d).symm

/-- The prescribed local map a_i: exchange for the actual inverse-coordinate square,
canonical Tate identification, comparison with the ordered tower, and its actual counit.
Source: blueprint order 1972, a_i (blueprint: proposition-purity-vector-bundles). -/
def vectorIntegrationLocalTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A V.ι).obj (vectorIntegrationSource A N hA S d F) ⟶
      ordinaryFiniteUnit A V.toScheme :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  (rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationChart_isPullback S d F V e)).app
        (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection V.toScheme d)).map
      (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
    (affineLinearCompactComparison N hN A hA V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d).inv ≫
    affineTraceCounit A N hA t D V.toScheme (affineTracePullbackInvertible N V.ι hS) d

/-- The defining local normalization on every Zariski linear trivialization. Quantifying
normalized projective-line data avoids making any such datum an extra hypothesis or a
choice in the global map: the Kummer and counit normalizations fix the actual trace.
Source: blueprint order 1972, uniqueness paragraph (blueprint: proposition-purity-vector-bundles).
-/
def VectorIntegrationNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (f : vectorIntegrationSource A N hA S d F ⟶ ordinaryFiniteUnit A S) : Prop :=
  ∀ (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
    (ordinaryFinitePullback A V.ι).map f ≫ (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS d F V e

/-- The bundle compact-support complex has no cohomology outside degree zero.
Source: blueprint vector integration, concentration paragraph.
(blueprint: lem-amb-vector-integration-cohomology-zero).

Proof: choose a finite-rank frame cover. Exchange, coefficient descent and the affine
trace identify each restriction with the constant complex. Exact inverse image commutes
with cohomology. The cover detects that the map of each other cohomology sheaf to zero
is an isomorphism. This also applies to the empty base and to rank zero. -/
theorem vectorIntegration_cohomology_zero (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (vectorIntegrationSource A N hA S d F)) := by
  classical
  obtain ⟨t, D, _, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  let M := (_root_.DerivedCategory.homologyFunctor _ q).obj
    (vectorIntegrationSource A N hA S d F)
  have hz : IsIso (0 : M ⟶ 0) := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A)
      (fun i : I ↦ (V i).ι) ?_ _ fun i ↦ ?_
    · intro x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    · let : TopologicalSpace.NoetherianSpace (V i).toScheme :=
        (V i).ι.isOpenEmbedding.isInducing.noetherianSpace
      let : IsNoetherian (V i).toScheme :=
        { toIsLocallyNoetherian := inferInstance
          isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
      let := (vectorIntegration_geometry S d F).1
      let := (vectorIntegration_geometry S d F).2.1
      let hi := affineTracePullbackInvertible N (V i).ι hS
      let := (htrace (V i).toScheme hi d).2.2.1
      let := isIso_rightDerivedLowerShriekBaseChangeMap A
        (vectorIntegrationChart_isPullback S d F (V i) (e i).some)
      have hl : IsIso (vectorIntegrationLocalTrace N hN A hA t D S hS d F
          (V i) (e i).some) := by
        dsimp only [vectorIntegrationLocalTrace]
        infer_instance
      let z := asIso (vectorIntegrationLocalTrace N hN A hA t D S hS d F
        (V i) (e i).some)
      have hunit : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (ordinaryFiniteUnit A (V i).toScheme)) := by
        rcases lt_or_gt_of_ne hq with hq | hq
        · exact _root_.DerivedCategory.isZero_of_isGE _ 0 q hq
        · exact _root_.DerivedCategory.isZero_of_isLE _ 0 q hq
      have hlocal := hunit.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso z)
      let b := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (V i).ι
      let c := (upperStar (ModuleCat.{u + 1} A) (V i).ι).mapDerivedCategoryHomologyFunctorIso q
      have hM : IsZero ((upperStar (ModuleCat.{u + 1} A) (V i).ι).obj M) :=
        hlocal.of_iso ((c.app _) ≪≫
          (_root_.DerivedCategory.homologyFunctor _ q).mapIso (b.app _).symm)
      exact isIso_of_source_target_iso_zero _ hM.isoZero
        (((upperStar (ModuleCat.{u + 1} A) (V i).ι).map_isZero
          (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))

end AlgebraicGeometry.Etale
