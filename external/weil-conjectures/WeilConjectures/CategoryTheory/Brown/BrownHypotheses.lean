/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCoefficientIso
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesFiniteCdFiniteCompact
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesFiniteCdNonfiniteCompact
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesFiniteCdIntegralExt
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
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
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic

/-!
# Hypotheses of Brown representability

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses/_section.md.
The main theorem assumes finite ℓ-cohomological dimension of the base field, as the blueprint's
compactness input does (proposition-compactness-finite-coefficients: "finite type over the base
field, so all cd_ℓ are finite"); the former arbitrary-field statement was false. The bundle lives
in `BrownHypothesesDefinitions`; proved criteria and conditional obstructions live in
`BrownHypothesesCriteria`. The integral and rational specializations below retain the
finite or separably closed base-field hypothesis of the upstream Ext bounds.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

open scoped CategoryTheory.Obj in
private theorem ordinary_constructible_of_constant_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  classical
  rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩] at hM
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let φ := condensedPullbackHom Λ (S.immersion a)
  have h := (hS a).isLocallyFinitelyPresented _
  unfold CondensedRing.upperStar at h
  exact lfp_of_comap (inv φ)
    (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))

open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
private theorem rational_brown_of_single_compact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hcons : ∀ M, IsConstantModelConstructible Λ X M →
      IsConstructibleModuleObject (condensedRingObj Λ X) M)
    (hsingle : ∀ M (_hM : IsConstantModelConstructible Λ X M)
      (hL : (boundedConstructible (condensedRingObj Λ X)).localizingClosure
        ((DerivedCategory.singleFunctor _ 0).obj M)),
      BrownRepresentability.IsCompactObj
        (⟨(DerivedCategory.singleFunctor _ 0).obj M, hL⟩ :
          (boundedConstructible (condensedRingObj Λ X)).localizingClosure.FullSubcategory))
    (hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory)
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj) :
    @IsCompactObject _ _ _ hSums K := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let H : ObjectProperty A := IsConstantModelConstructible Λ X
  let B := boundedConstructible (condensedRingObj Λ X)
  let P := B.localizingClosure
  let L := localizingClosureProEtale Λ X
  let _ : H.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  obtain ⟨hamb, _, _, hloc, _, _⟩ := localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K)
  let _ := hamb
  let _ : L.IsTriangulated := hloc.1
  let _ : L.IsClosedUnderIsomorphisms := hloc.2.1
  have hclosed (I : Type (u + 2)) : L.IsClosedUnderColimitsOfShape (Discrete I) :=
    hloc.isClosedUnderColimitsOfShape_discrete I
  let _ (I : Type (u + 1)) : L.IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
  let _ (I : Type (u + 2)) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    closedUnderCoproducts_of_small P (fun _ ↦ inferInstance) I
  have hLP : L ≤ P := by
    intro M hM
    exact hM P ⟨inferInstance, inferInstance, fun F hF hFP ↦
      P.prop_of_isColimit (colimit.isColimit F) (fun i ↦ hFP i.as)⟩
      (fun N hN ↦ B.le_localizingClosure N ⟨hN.1.1, fun n ↦ hcons _ (hN.1.2 n)⟩)
  apply compact_devissage_and_restrict H P L hLP ?_ K hK
  intro M hM
  have hB : B ((DerivedCategory.singleFunctor A 0).obj M) := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
    by_cases hn : n = 0
    · subst n
      exact hcons _ (H.prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app M).symm hM)
    · exact isConstructibleModuleObject_of_isZero _ (by
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact DerivedCategory.isZero_of_isGE _ 0 n hn
        · exact DerivedCategory.isZero_of_isLE _ 0 n hn)
  let hP := B.le_localizingClosure _ hB
  exact ⟨hP, (isCompactObject_iff_isCompactObj _).mpr (hsingle M hM hP)⟩

open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
/-- Brown representability hypotheses for a separated finite-type scheme in positive
characteristic different from the coefficient prime, for exactly the admissible rings.
`IsLocalizingAdmissibleCoefficient` specifies the six concrete coefficient objects up to
ring-object isomorphism, including the discrete finite rings killed by a power of `ℓ`.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md and sk-lem-brown-hypotheses.proof.md
(blueprint: lemma-hypotheses-brown-representability).

Proof: First unpack lemma-hypotheses-brown-representability--1: the datum is a prime ℓ, a field of
characteristic p > 0 distinct from ℓ with cd_ℓ(k) < ∞ (definition-cohomological-dimension), and a
separated finite-type k-scheme X; by Stacks 0F10 all cd_ℓ in the setting are then finite.
Unpack definition-localizing-subcategory: Λ is one of the six specified condensed rings;
the ambient category is the unbounded derived category of modules over Λ_X;
S is the bounded constructible finite-Tor property and L is its replete localizing
intersection, with coproducts in the fixed universe and no completeness restriction.
Second apply lemma-hypotheses-brown-representability to this datum to obtain local smallness,
triangulation, arbitrary sums and split idempotents of L. Apply
 lemma-hypotheses-brown-representability--5 to obtain thickness and essential smallness of S.
Choosing one representative per isomorphism class gives a small skeleton.
Third let G be any such skeleton and apply lemma-hypotheses-brown-representability:
each representative is compact in L, and vanishing of Hom(C[n], K) for all
representatives C and all integers n forces K to be zero. Compactness is exactly
lemma-hypotheses-brown-representability--1. To identify the second conclusion with
lemma-hypotheses-brown-representability--1, use Hom(coproduct C, K[-n]) = product Hom(C[n], K). If
every morphism from the coproduct into every shift of K is zero, the component Hom groups vanish,
so K is zero; contrapositively every nonzero K receives a nonzero map from the
coproduct into some shift. This is IsTriangulatedGeneratingFamily. All these
arguments apply to every small skeleton, with the inherited shift and any chosen
coproduct universal properties. -/
theorem brownHypotheses
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (hcd : AlgebraicGeometry.ProEtale.cohomologicalDimension ℓ (Fact.out : ℓ.Prime)
      (Spec (.of k)) < ⊤)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let _ : Fact (ringChar k ≠ ℓ) := ⟨(ringChar.eq k p) ▸ hpl⟩
  obtain ⟨hpadic, hE, hbar⟩ :=
    brownHypotheses_rational_uniformExtBound_of_finite_cd ℓ hcd aX
  have hOE := brownHypotheses_integral_uniformExtBound_of_finite_cd ℓ hcd aX
  have hfrom (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R] (hR : IsLocalizingAdmissibleCoefficient ℓ R)
      (hh : IsIndConstructibleHeart (condensedRingObj R X))
      (hc : HasConstructibleExtContinuity (condensedRingObj R X))
      (hb : HasUniformConstructibleExtBound (condensedRingObj R X)) :
      BrownHypothesesFor R X := by
    obtain ⟨_, _, _, _, hSums, _⟩ := brownHypotheses_structural R X
    apply (brownHypothesesFor_iff_compact_of_noetherian ℓ X R hR).mpr
    refine ⟨hSums, fun K hK ↦ ?_⟩
    apply rational_brown_of_single_compact R X
      (ordinary_constructible_of_constant_model R X) ?_ hSums K hK.1
    intro M hM hL
    exact isCompactObj_singleFunctor_of_isIndConstructibleHeart hh
      (.of_continuity hc hb) M (ordinary_constructible_of_constant_model R X M hM) hL
  have hi (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      BrownHypothesesFor (Profinite.padicIntegersRingObj.{u} ℓ E) X := by
    apply hfrom _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))))
    · exact CondensedRing.isIndConstructibleHeart_padicIntegersRingObj ℓ E aX
    · exact CondensedRing.hasConstructibleExtContinuity_padicIntegersRingObj ℓ E aX
    · exact hOE E
  have hq (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      BrownHypothesesFor (Profinite.continuousMapRingObj.{u} E) X := by
    apply hfrom _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
    · exact CondensedRing.isIndConstructibleHeart_continuousMapRingObj ℓ E aX
    · exact CondensedRing.hasConstructibleExtContinuity_continuousMapRingObj ℓ E aX
    · exact hE E
  rcases hΛ with hfinite | hz | hqpadic | he | hoe | hqbar
  · exact (brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ (Or.inl hfinite)).mpr
      (brownHypotheses_compact_of_finite_cd_finite ℓ p hp hpl hcd aX Λ hfinite)
  · obtain ⟨e⟩ := hz
    apply (brownHypothesesFor_coefficientIso_iff e X).mpr
    obtain ⟨_, _, _, _, _, _, _, _, _, zIso, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact (brownHypothesesFor_coefficientIso_iff zIso X).mpr (hi ⟨⊥, inferInstance⟩)
  · obtain ⟨e⟩ := hqpadic
    apply (brownHypothesesFor_coefficientIso_iff e X).mpr
    apply hfrom _ (Or.inr (Or.inr (Or.inl ⟨Iso.refl _⟩)))
    · exact CondensedRing.isIndConstructibleHeart_continuousMapRingObj ℓ ℚ_[ℓ] aX
    · exact CondensedRing.hasConstructibleExtContinuity_continuousMapRingObj ℓ ℚ_[ℓ] aX
    · exact hpadic
  · obtain ⟨E, ⟨e⟩⟩ := he
    exact (brownHypothesesFor_coefficientIso_iff e X).mpr (hq E)
  · obtain ⟨E, ⟨e⟩⟩ := hoe
    exact (brownHypothesesFor_coefficientIso_iff e X).mpr (hi E)
  · obtain ⟨e⟩ := hqbar
    apply (brownHypothesesFor_coefficientIso_iff e X).mpr
    apply hfrom _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))))
    · exact CondensedRing.isIndConstructibleHeart_padicAlgClRingObj ℓ aX
    · exact CondensedRing.hasConstructibleExtContinuity_padicAlgClRingObj ℓ aX
    · exact hbar

end CategoryTheory
