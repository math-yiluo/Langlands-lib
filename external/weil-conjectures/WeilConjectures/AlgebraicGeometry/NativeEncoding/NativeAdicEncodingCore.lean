/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Native adic encoding, independently of Weil fixed pairs

## Implementation details

These native declarations do not import the Weil-sheaf files, so that they are available
before native finiteness.

## References

* Bhatt--Scholze, Definitions 6.8.1 and 6.8.3
* Bhatt--Scholze 6.8.1--6.8.3
* Stacks 03EK
* Stacks 015F and 070I
* Stacks 03D6--03D7
* Stacks 070I and 070Y
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonObj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.NativeEncoding

/-- The normalized coefficient isomorphism used in the ring-realization theorem. -/
abbrev coefficientIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    condensedRingObj (Profinite.padicAlgClRingObj l) T ≅
      (weilCoefficientsForgetAb l T).obj (adicConstantSheaf l T) :=
  (Mon.forget _).mapIso (CondensedQbarCoefficientRealization.globalCoefficientIso l T) ≪≫
    padicAlgClSheafIsoAdicConstantSheaf T l

/-- The same ring isomorphism respects multiplication and the unit. -/
@[instance] theorem coefficientIsoMon (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    IsMonHom (coefficientIso l T).hom := by
  change IsMonHom
    ((CondensedQbarCoefficientRealization.globalCoefficientIso l T).hom.hom ≫
      padicAlgClSheafToAdicConstantSheaf T l)
  infer_instance

/-- Forget vector scalars in the native action and restrict it along theta.
The lax tensorator imposes precisely the original balanced vector-space action. -/
def encoding (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    AdicSheaf l T ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T) :=
  AdicSheaf.forgetAb l T ⋙ Mod.comap (coefficientIso l T).hom

/-- The encoding is additive, with its existing action on underlying morphisms. -/
@[instance] theorem encodingAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (encoding l T).Additive := by
  constructor
  intro M N f g
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  ext V m
  rfl

/-- The specified encoding is an equivalence, rather than an arbitrary equivalence of hearts. -/
@[instance] theorem encoding_isEquivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (encoding l T).IsEquivalence := by
  have : (AdicSheaf.forgetAb l T).IsEquivalence :=
    nativeScalarForgetting_isEquivalence l T
  have : (Mod.comap (coefficientIso l T).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (coefficientIso l T).hom).isEquivalence_functor
  change (AdicSheaf.forgetAb l T ⋙ Mod.comap (coefficientIso l T).hom).IsEquivalence
  infer_instance

/-- The equivalence with the specified forward encoding; its inverse is determined by it. -/
def equivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  (encoding l T).asEquivalence

/-- The localization of this exact encoding on ordinary unbounded derived categories. -/
abbrev derivedEncoding (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  (encoding l T).mapDerivedCategory

/-- Exactness and the unbounded derived equivalence, including preservation and reflection
of K-injectivity. -/
theorem encoding_exact_derived (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    PreservesFiniteLimits (encoding l T) ∧ PreservesFiniteColimits (encoding l T) ∧
      (derivedEncoding l T).IsEquivalence ∧
      (∀ I : CochainComplex (AdicSheaf l T) ℤ,
        CochainComplex.IsKInjective (((encoding l T).mapHomologicalComplex (.up ℤ)).obj I) ↔
          I.IsKInjective) := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun I ↦ ?_⟩
  let e := equivalence l T
  have : e.functor.Additive := inferInstanceAs (encoding l T).Additive
  have : e.inverse.Additive := e.inverse_additive
  constructor
  · intro h
    have : CochainComplex.IsKInjective
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj I) := h
    have : e.inverse.IsEquivalence := inferInstance
    have : CochainComplex.IsKInjective
        ((e.inverse.mapHomologicalComplex (.up ℤ)).obj
          ((e.functor.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
    exact CochainComplex.isKInjective_of_iso
      (L₁ := (e.inverse.mapHomologicalComplex (.up ℤ)).obj
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj I))
      (((e.mapHomologicalComplex (.up ℤ)).unitIso.app I).symm)
  · intro h
    have := h
    infer_instance


private lemma finiteComparison_eq_chart (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (CondensedQbarCoefficientRealization.fieldDiagramIso ℓ T).hom.app E =
      chartComparison T E := by
  unfold CondensedQbarCoefficientRealization.fieldDiagramIso
  change (CondensedQbarCoefficientRealization.finiteFieldComparisonIso E ℓ T).hom.hom = _
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ _ = adj.homEquiv _ _ ((adj.homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply]
  ext S f
  exact CondensedQbarCoefficientRealization.finiteFieldComparison_test E ℓ T S.unop f.down

private lemma finiteLeg_native (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : T.ProEtᵒᵖ)
    (s : ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf T E)).obj.obj V) (x : V.unop.left) :
    (((((padicAlgClSheafCocone T ℓ).ι.app E ≫
      padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V) s).down.1 x) =
        (s.down x : PadicAlgCl ℓ) := by
  let J := Scheme.ProEt.topology T
  let R := padicSubfieldSheaf T ℓ E.1
  let RAb := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hu : (Sheaf.sheafifyRingPresheafIso J R).inv.hom = toSheafify J RAb.obj := by
    change (sheafToPresheaf J Ab.{u + 1}).map
      (inv ((sheafificationAdjunction J Ab.{u + 1}).counit.app RAb)) = _
    rw [Functor.map_inv]
    exact (sheafificationAdjunction J Ab.{u + 1}).inv_counit_map
  have hf : toSheafify J (padicAlgClRingPresheaf T ℓ ⋙ forget₂ RingCat Ab) ≫
      (padicAlgClSheafToAdicConstantSheaf T ℓ).hom =
        padicAlgClPresheafToAdicConstantSheaf T ℓ := by
    exact ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _
  change (((((padicSubfieldSheafToPadicAlgClSheaf T ℓ E.1) ≫
    padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V) s).down.1 x) = _
  unfold padicSubfieldSheafToPadicAlgClSheaf continuousMapRingSheafToPadicAlgClSheaf
    Sheaf.sheafComposeToSheafify
  change ((((((Sheaf.sheafifyRingPresheafIso J R).inv.hom ≫ _) ≫
    (padicAlgClSheafToAdicConstantSheaf T ℓ).hom).app V) s).down.1 x) = _
  rw [hu, Category.assoc, ← toSheafify_naturality_assoc, hf]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma coefficient_pushforward_naturality
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Γ] (a : Λ ⟶ Γ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPoint Y).map a ≫ condensedPushforwardHom Γ f =
      condensedPushforwardHom Λ f ≫
        (lowerStar Ab.{u + 1} f).map ((upperStarFromPoint X).map a) := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  have hu := adj.unit.naturality ((upperStarFromPoint Y).map a)
  have hn := (upperStarFromPointComp f).hom.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu hn
  change (upperStarFromPoint Y).map a ≫
      adj.unit.app ((upperStarFromPoint Y).obj Γ) ≫
        (lowerStar Ab.{u + 1} f).map ((upperStarFromPointComp f).hom.app Γ) =
    (adj.unit.app ((upperStarFromPoint Y).obj Λ) ≫
      (lowerStar Ab.{u + 1} f).map ((upperStarFromPointComp f).hom.app Λ)) ≫ _
  rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
    hn, Functor.map_comp, Category.assoc]

private lemma finiteLeg_native_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ((padicAlgClSheafCocone Y ℓ).ι.app E ≫ padicAlgClSheafToAdicConstantSheaf Y ℓ) ≫
        (weilCoefficientsForgetAb ℓ Y).map (adicConstantSheafToLowerStar ℓ f) =
      CondensedRing.continuousFunctionPushforward f E ≫
        (lowerStar Ab.{u + 1} f).map
          ((padicAlgClSheafCocone X ℓ).ι.app E ≫ padicAlgClSheafToAdicConstantSheaf X ℓ) := by
  ext V s
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, lowerStar_map_hom_app']
  change (((((padicAlgClSheafCocone Y ℓ).ι.app E ≫
    padicAlgClSheafToAdicConstantSheaf Y ℓ).hom.app V) s).down.1
      ((CategoryTheory.Limits.pullback.fst V.unop.hom f) x)) = _
  rw [finiteLeg_native]
  change (s.down ((CategoryTheory.Limits.pullback.fst V.unop.hom f) x) : PadicAlgCl ℓ) =
    (((((padicAlgClSheafCocone X ℓ).ι.app E ≫
      padicAlgClSheafToAdicConstantSheaf X ℓ).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V.unop)))
          ((CondensedRing.continuousFunctionPushforward f E).hom.app V s)).down.1 x)
  rw [finiteLeg_native, CondensedRing.continuousFunctionPushforward_app]
  rfl

private lemma coefficientIso_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (h : X ⟶ Y) :
    condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) h ≫
        (lowerStar Ab.{u + 1} h).map (coefficientIso ℓ X).hom =
      (coefficientIso ℓ Y).hom ≫
        (weilCoefficientsForgetAb ℓ Y).map (adicConstantSheafToLowerStar ℓ h) := by
  let θ (T : Scheme.{u}) := coefficientIso ℓ T
  have hθ (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
        (θ T).hom = chartComparison T E ≫
          (padicAlgClSheafCocone T ℓ).ι.app E ≫
            padicAlgClSheafToAdicConstantSheaf T ℓ := by
    change (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
      ((CondensedQbarCoefficientRealization.globalCoefficientIso ℓ T).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf T ℓ) = _
    rw [← Category.assoc,
      CondensedQbarCoefficientRealization.globalCoefficientIso_fac, finiteComparison_eq_chart,
      Category.assoc]
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint Y) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))).leftAdjoint_preservesColimits
  apply (isColimitOfPreserves (upperStarFromPoint Y)
    (Profinite.isColimitPadicAlgClRingObjCocone ℓ)).hom_ext
  intro E
  change (upperStarFromPoint Y).map
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫ _ =
      (upperStarFromPoint Y).map
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫ _
  rw [← Category.assoc, coefficient_pushforward_naturality, Category.assoc,
    ← Functor.map_comp, hθ, Functor.map_comp, ← Category.assoc,
    CondensedRing.continuousChart_scheme_naturality, Category.assoc,
    ← finiteLeg_native_naturality, ← Category.assoc, ← hθ, Category.assoc]

@[irreducible] private noncomputable def nativePushforwardComparison (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) :
    adicLowerStar ℓ h ⋙ encoding ℓ T ≅
      encoding ℓ S ⋙ CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) h := by
  let θ (T : Scheme.{u}) := coefficientIso ℓ T
  letI (X : Scheme.{u}) : IsMonHom (θ X).hom :=
    coefficientIsoMon ℓ X
  let L := lowerStar (WeilCoefficients.{u} ℓ) h
  let U := weilCoefficientsForgetAb ℓ T
  let V := weilCoefficientsForgetAb ℓ S
  let R := lowerStar Ab.{u + 1} h
  let B := adicConstantSheaf ℓ S
  let e := lowerStarCompWeilCoefficientsForgetAbIso ℓ h
  let a := (θ T).hom ≫ U.map (adicConstantSheafToLowerStar ℓ h)
  have ha : IsMonHom a := by dsimp [a]; infer_instance
  let e₁ : adicLowerStar ℓ h ⋙ encoding ℓ T ≅
      (V ⋙ R).mapMod B ⋙ Mod.comap
        ((θ T).hom ≫ U.map (adicConstantSheafToLowerStar ℓ h) ≫
          Functor.compAlgHom L U e.hom B) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (U.mapModComapIso (adicConstantSheafToLowerStar ℓ h)) _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapModCompIso L U e.hom B) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)
  let e₂ : encoding ℓ S ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) h ≅
      (V ⋙ R).mapMod B ⋙ Mod.comap
        (condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) h ≫ R.map (θ S).hom ≫
          Functor.compAlgHom V R (𝟙 (V ⋙ R)) B) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (R.mapModComapIso (θ S).hom) _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapModCompIso V R (𝟙 (V ⋙ R)) B) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)
  refine e₁ ≪≫ Functor.isoWhiskerLeft _ (Mod.comapCongr ?_) ≪≫ e₂.symm
  simp only [Functor.compAlgHom, NatTrans.id_app]
  exact (coefficientIso_naturality ℓ h).symm

set_option backward.isDefEq.respectTransparency false in
private theorem nativePushforwardComparison_hom (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : AdicSheaf ℓ X) :
    (((nativePushforwardComparison ℓ f).hom.app M).hom) = 𝟙 _ := by
  simp only [nativePushforwardComparison, Functor.isoWhiskerLeft_trans,
    Functor.mapModComapIso_hom_app_hom, Functor.mapModComapIso_inv_app_hom,
    Functor.mapModCompIso_hom_app_hom, Functor.mapModCompIso_inv_app_hom,
    Mod.comapCongr_hom_app_hom,
    Iso.trans_assoc, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_hom,
    Iso.symm_inv, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.comp_map,
    Category.comp_id, Category.id_comp, Mod.comp_hom', Mod.id_hom', Mod.comap_map_hom,
    Mod.comapComp_inv_app_hom, Mod.comapComp_hom_app_hom, Iso.refl_hom,
    NatTrans.id_app]
  erw [IsIso.inv_id]
  repeat' erw [Category.id_comp]
  rfl

private theorem inverseMate_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : TwoSquare R₁ H G R₂)
    [IsIso (((mateEquiv adj₁ adj₂).symm β))] :
    (mateEquiv adj₁ adj₂
      (asIso (((mateEquiv adj₁ adj₂).symm β))).symm.inv) =
        β := by
  change ((mateEquiv adj₁ adj₂) ((mateEquiv adj₁ adj₂).symm β)) = _
  exact congrArg (fun s : TwoSquare R₁ H G R₂ ↦ s)
    ((mateEquiv adj₁ adj₂).apply_symm_apply β)

/-- The actual underived direct image and ringed module pullback are identified. -/
theorem encoding_ordinary_operations (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ p : adicLowerStar l f ⋙ encoding l Y ≅
        encoding l X ⋙ CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f,
      (∀ (M : AdicSheaf l X) (V : Y.ProEtᵒᵖ)
        (m : ((adicLowerStar l f).obj M).X.obj.obj V),
        ((p.hom.app M).hom.hom.app V) m = m) ∧
      ∃ q : adicUpperStar l f ⋙ encoding l X ≅
          encoding l Y ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f,
      (mateEquiv (adicUpperStarLowerStarAdjunction l f)
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
        q.inv) = p.hom ∧
      PreservesFiniteLimits (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f) ∧
      PreservesFiniteColimits (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f) ∧
      (condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
          (lowerStar Ab.{u + 1} f).map (coefficientIso l X).hom =
        (coefficientIso l Y).hom ≫
          (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f)) := by
  let p := nativePushforwardComparison l f
  let α := ((mateEquiv (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)).symm
      p.hom)
  have : IsIso α := isIso_inverseMate_of_equivalences
    (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f) p
  refine ⟨p, ?_, (asIso α).symm, ?_, inferInstance, inferInstance,
    coefficientIso_naturality l f⟩
  · intro M V m
    exact congrArg (fun k ↦ (k.hom.app V) m)
      (nativePushforwardComparison_hom l f M)
  · exact inverseMate_mate (adicUpperStarLowerStarAdjunction l f)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (TwoSquare.mk _ _ _ _ p.hom)

/-- The identity-on-sections direct-image comparison. Its normalization determines it uniquely. -/
def pushComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Classical.choose (encoding_ordinary_operations l f)

/-- The ordinary pullback comparison, uniquely fixed as the mate of pushComparison. -/
def pullComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Classical.choose (Classical.choose_spec (encoding_ordinary_operations l f)).2

/-- Canonical right derivation of the normalized ordinary direct-image comparison.
All factors are universal derived comparisons, computed using the same K-injectives. -/
def derivedPushComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (adicLowerStar l f).rightDerivedFunctor ⋙ derivedEncoding l Y ≅
      derivedEncoding l X ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (adicLowerStar l f)
    (encoding l Y)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (pushComparison l f) ≪≫
  Functor.rightDerivedFunctorCompIso (encoding l X)
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f) ≪≫
  Functor.isoWhiskerRight (encoding l X).rightDerivedFunctorIsoMapDerivedCategory _

end AlgebraicGeometry.ProEtale.NativeEncoding
