/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionTheorem
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocalizedRingMateGraph
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSized
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarExtensionSliceComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocalizedRingMateGraphEvaluation
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalized continuous coefficient restriction to a pro-etale slice

Source: Bhatt--Scholze, Definition 6.8.1, Lemma 6.8.2, paragraph before Definition
6.8.6 and Remark 6.8.15; Stacks, Tags 00VC, 00XZ, 03EL, 06YY and 0G7E
(blueprint: lem-per-continuous-coefficient-slice-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ContinuousSlice

/-- Literal module restriction along composition with a site object. The scalar ring
is the literal restriction of R; both sections and morphisms are precomposed.
Source: Stacks 00XZ and 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def modules {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcModules X R ⥤ pbcModules U.left
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) :=
  letI : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  SheafOfModules.pushforward (F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop)
    (J := ProEt.topology U.left) (K := ProEt.topology X) (𝟙 _)

private theorem exact_moduleRestriction
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.IsCocontinuous J K] [F.IsLeftAdjoint]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) [IsIso φ] :
    (SheafOfModules.pushforward.{u} φ).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) :=
    preservesFiniteLimits_of_reflects_of_preserves _ T
  have : (SheafOfModules.pushforward.{u} φ).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso φ
  refine ⟨?_, inferInstance, inferInstance⟩
  constructor
  intro M N f g
  apply SheafOfModules.hom_ext
  ext V m
  rfl

/-- Exactness of literal restriction, including nonnoetherian U.
Source: Stacks 00XZ, 03EL and 03CZ
(blueprint: lem-per-continuous-coefficient-slice-normalization).
Proof: the forgetful functor to module presheaves reflects finite limits, and
presheaf restriction preserves them. Composition with U is cocontinuous and left
adjoint to base change, giving the left-adjoint property of module restriction
and preservation of colimits. Additivity is checked on sections. No coefficient
flatness, boundedness or noetherian hypothesis on U is used. -/
theorem modules_exact {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (modules U R).Additive ∧ PreservesFiniteLimits (modules U R) ∧
      PreservesFiniteColimits (modules U R) := by
  let G := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  let : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let : G.IsCocontinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap U.prop
  let : G.IsLeftAdjoint :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial).isLeftAdjoint
  exact exact_moduleRestriction (F := G) (𝟙 _)

/-- The additive structure supplied by exact restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_additive {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : (modules U R).Additive :=
  (modules_exact U R).1

/-- Finite limits preserved by restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_limits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (modules U R) := (modules_exact U R).2.1

/-- Finite colimits preserved by restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_colimits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (modules U R) := (modules_exact U R).2.2

/-- Unbounded derived restriction is exact termwise restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def derived {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (modules U R).mapDerivedCategory

/-- The coefficient identification is the identity on continuous functions on V.
Source: Bhatt--Scholze 6.8.1; Stacks 00XZ
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def ring {X : Scheme.{u}} (U : X.ProEt) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      U.hom U.prop).obj (continuousCoefficientSheaf X T) ≅
      continuousCoefficientSheaf U.left T :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- Actual inverse image is normalized by its Kan coprojections and sheafification
unit, and its coefficient structural map becomes the identity on the same V.
Source: Bhatt--Scholze 6.8.1; Stacks 00VC and 00XZ
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Coefficients {X : Scheme.{u}} (U : X.ProEt) where
  sets : ProEtaleObjectRestrictionComparison U (Type (u + 1))
  groups : ProEtaleObjectRestrictionComparison U AddCommGrpCat.{u + 1}
  rings : ProEtaleObjectRestrictionComparison U RingCat.{u + 1}
  commRings : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}
  initial : ∀ V : U.left.ProEt,
    Nonempty (IsInitial (proEtaleObjectInverseImageIndexPoint U V))
  continuous : ∀ (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T],
    IsIso (continuousCoefficientPullback T U.hom) ∧
      continuousCoefficientPullback T U.hom =
        commRings.sheafIso.hom.app (continuousCoefficientSheaf X T) ≫ (ring U T).hom
  constants : ∀ (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T] (V : U.left.ProEt) (a : T),
    (ring U T).hom.hom.app (op V)
      (ContinuousMap.const V.left a) = ContinuousMap.const V.left a
  coefficient_maps : ∀ (T S : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T] [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
      (h : T →+* S) (hc : Continuous h),
    (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).map
        (continuousCoefficientMap h hc X) ≫ continuousCoefficientPullback S U.hom =
      continuousCoefficientPullback T U.hom ≫ continuousCoefficientMap h hc U.left
  finite : ∀ (A : CommRingCat.{u + 1}) [Finite A],
    IsIso (proEtaleConstantInverseImageMap U.hom CommRingCat.{u + 1} A)

private theorem continuous_pullback_slice {X : Scheme.{u}} (U : X.ProEt)
    (b : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})
    (bA : ProEtaleObjectRestrictionComparison U AddCommGrpCat.{u + 1})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    continuousCoefficientPullback T U.hom =
      b.sheafIso.hom.app (continuousCoefficientSheaf X T) ≫ (ring U T).hom := by
  let R := continuousCoefficientSheaf X T
  let S := continuousCoefficientSheaf U.left T
  let beta := b.sheafIso.app R ≪≫ ring U T
  have h := (proEtaleLocalizedRingMateGraphEvaluation U b bA R S beta).1
  apply ((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).homEquiv R S).injective
  erw [continuousCoefficientPullback, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change C(V.unop.left, T) at s
  change _ = (ring U T).hom.hom.app _
    ((b.sheafIso.hom.app R).hom.app _
      (((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).unit.app R).hom.app V s))
  erw [h]
  rfl

private theorem coefficients_exists {X : Scheme.{u}} (U : X.ProEt) :
    Nonempty (Coefficients U) := by
  obtain ⟨h0, ⟨s⟩, ⟨a⟩, ⟨r⟩, c, e, he, hc, hM⟩ :=
    proEtaleObjectInverseImageRestriction X U (ULift.{u} ℤ)
  refine ⟨⟨s, a, r, c, h0, ?_, ?_, ?_, ?_⟩⟩
  · intro T _ _ _
    have h := continuous_pullback_slice U c a T
    refine ⟨?_, h⟩
    rw [h]
    infer_instance
  · intro T _ _ _ V x
    rfl
  · intro T S _ _ _ _ _ _ f hf
    exact continuousCoefficientPullback_naturality f hf U.hom
  · intro A _
    let Q := (Functor.const ℕᵒᵖ).obj A
    let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun _ ↦ inferInstanceAs (Finite A)
    exact (proEtale_profinite_coefficient_inverse_image Q).1 U.left X U.hom (op 0)

/-- The residue projections to the actual finite constant sheaves, using the canonical
constant-function comparison, not an arbitrary identification of the quotient.
Source: Bhatt--Scholze 6.8.1--6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def residue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    integralCoefficientSheaf l X E ⟶ (finiteCoefficientTower l X E).obj (op n) :=
  continuousCoefficientReduction l E X n ≫ (discreteContinuousCoefficientIso X).inv.app
    (finiteCoefficientRing l E n)

private theorem constantComparison_pullback (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (continuousCoefficientConstantComparison X T) ≫ continuousCoefficientPullback T h =
      proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of T) ≫
        continuousCoefficientConstantComparison Z T := by
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  change _ ≫ (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T)) _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  unfold continuousCoefficientConstantComparison proEtaleConstantDirectImageMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  have hz := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj (CommRingCat.of T)) (continuousCoefficientSheaf Z T))
    (continuousCoefficientConstants Z T)
  exact (congrArg (fun f ↦ f.app ((proEtaleBaseChange h).op.obj U)) hz).symm

/-- The completed and localized coefficient identifications with their canonical projections.
Source: Bhatt--Scholze 6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Completion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) where
  integral : integralCoefficientSheaf l X E ≅ finiteCoefficientLimit l X E
  projections : ∀ n : ℕ,
    integral.hom ≫ limit.π (finiteCoefficientTower l X E) (op n) = residue l E X n
  rational : integralCoefficientLocalization l X E ≅ rationalCoefficientSheaf l X E
  fractions : integralCoefficientLocalizationNormalized l E X rational.hom

private theorem completion_exists (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Nonempty (Completion l E X) := by
  classical
  let := coefficientExtensionNormedField l E
  let e := Functor.isoWhiskerLeft (finiteCoefficientRingTower l E)
    (discreteContinuousCoefficientIso X)
  let hc := Classical.choice (continuousCoefficientResidueCone_isLimit l E X)
  let i := hc.conePointsIsoOfNatIso (limit.isLimit (finiteCoefficientTower l X E)) e.symm
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  refine ⟨⟨i, ?_, b, hb⟩⟩
  intro n
  have h := hc.conePointsIsoOfNatIso_hom_comp
    (limit.isLimit (finiteCoefficientTower l X E)) e.symm (op n)
  exact h

private theorem ordinaryExtension {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    Nonempty (proEtaleModuleInverseImage f R ⋙ pbcExtend c.hom ≅
      proEtaleRingModulePullback f R S c) := by
  let I := proEtaleModuleInverseImage f R
  let hobj := (pbcExtensionExistence c.hom).choose_spec.choose
  refine ⟨NatIso.ofComponents (fun M ↦ eqToIso (hobj (I.obj M))) ?_⟩
  intro M N a
  change (pbcExtend c.hom).map (I.map a) ≫ eqToHom (hobj (I.obj N)) =
    eqToHom (hobj (I.obj M)) ≫ _
  erw [(pbcExtensionExistence c.hom).choose_spec.choose_spec.choose (I.map a)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

private theorem exactExtensionDerived {Y : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (φ : R ⟶ S)
    [PreservesFiniteLimits (pbcExtend φ)] [PreservesFiniteColimits (pbcExtend φ)] :
    ∃ d : pbcDerivedExtend φ ≅ (pbcExtend φ).mapDerivedCategory,
      ∀ P : CochainComplex (pbcModules Y R) ℤ,
        pbcComplexCounit φ P = d.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcExtend φ).mapDerivedCategoryFactors.hom.app P := by
  let L := pbcExtend φ
  let D := pbcDerivedExtend φ
  let ε := pbcExtensionCounit φ
  have : D.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (pbcModules Y R) (.up ℤ)) :=
    pbcDerivedExtension_universal φ
  have : L.mapDerivedCategory.IsLeftDerivedFunctor L.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (pbcModules Y R) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryFactorsh
  let d := Functor.leftDerivedUnique L.mapDerivedCategory D ε
    L.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (pbcModules Y R) (.up ℤ))
  have hd : Functor.whiskerLeft DerivedCategory.Qh d.hom ≫
      L.mapDerivedCategoryFactorsh.hom = ε := by
    simp [d]
  refine ⟨d, ?_⟩
  intro P
  have h := congrArg (fun t ↦ t.app ((HomotopyCategory.quotient _ _).obj P)) hd
  change _ = d.hom.app _ ≫ _
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  unfold pbcComplexCounit
  rw [← h, Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [L, D]
  simp only [Category.assoc, ← NatTrans.naturality_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact congrArg (fun f ↦ d.hom.app (DerivedCategory.Q.obj P) ≫ f)
    (Category.comp_id (L.mapDerivedCategoryFactors.hom.app P))

/-- Restricting an ambient derived tensor pullback is scalar extension on the restricted
inverse image. The counit equation specifies the comparison on K-flat representatives.
Source: Stacks 03EL, 06YS, 0G7E and 06YY
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Ambient {X Y : Scheme.{u}} (f : Y ⟶ X) (U : Y.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S) where
  ordinary : pbcExtend c ⋙ modules U S ≅
    modules U ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⋙
      pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).map c)
  sections : ∀ (M : pbcModules Y
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
      (V : U.left.ProEtᵒᵖ) (s : S.obj.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)))
      (m : M.val.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))),
    (ordinary.hom.app M).val.app V (pbcTensorSection c M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) s m) =
      pbcTensorSection ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c) ((modules U _).obj M) V s m
  complex : (pbcExtend c).mapHomologicalComplex (.up ℤ) ⋙
      (modules U S).mapHomologicalComplex (.up ℤ) ≅
    (modules U ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).mapHomologicalComplex
      (.up ℤ) ⋙
      (pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  scalar_derived : pbcDerivedExtend c ⋙ ContinuousSlice.derived U S ≅
    ContinuousSlice.derived U
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⋙
      pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)
  normalization : ∀ P : CochainComplex
      (pbcModules Y ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) ℤ,
    (ContinuousSlice.derived U S).map (pbcComplexCounit c P) ≫
        (modules U S).mapDerivedCategoryFactors.hom.app
          (((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complex.hom.app P) =
      scalar_derived.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)).map
          ((modules U _).mapDerivedCategoryFactors.hom.app P) ≫
        pbcComplexCounit ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)
          (((modules U _).mapHomologicalComplex (.up ℤ)).obj P)

/-- The ambient formula after the actual geometric inverse image. This is obtained by
whiskering the counit-normalized scalar comparison, so it is fixed on representatives.
Source: Stacks 06YY and 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def Ambient.pullback {X Y : Scheme.{u}} {f : Y ⟶ X} {U : Y.ProEt}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S}
    (a : Ambient f U R S c) :=
  Functor.isoWhiskerLeft (adicTowerPullback f R) a.scalar_derived

end AlgebraicGeometry.Scheme.ContinuousSlice
