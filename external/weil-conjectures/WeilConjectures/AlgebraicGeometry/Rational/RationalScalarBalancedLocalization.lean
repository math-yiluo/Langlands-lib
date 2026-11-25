/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionCoherence
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackIso
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientGeneralPullbackIso

/-! # Balanced localization of finite coefficient extensions

The coefficient map is postcomposition, not a chosen ring map. Tensor comparisons
are the existing unit-normalized comparisons. Raw fractions retain integral Hom torsion.

## References

* Stacks Project, Tags 0G7E and 0D6D
* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
* Stacks 00CO and 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)

/-- A finite coefficient embedding is continuous for the specified spectral topologies. -/
theorem rationalBalancedEmbedding_continuous :
    @Continuous E F
      ((coefficientExtensionNormedField l E).toMetricSpace.toPseudoMetricSpace.toUniformSpace
        ).toTopologicalSpace
      ((coefficientExtensionNormedField l F).toMetricSpace.toPseudoMetricSpace.toUniformSpace
        ).toTopologicalSpace i := by
  let := coefficientExtensionNormedField l E
  let := coefficientExtensionNormedField l F
  have hi : Isometry i := by
    apply AddMonoidHomClass.isometry_of_norm i
    intro x
    exact WeilConjectures.integralScalar_absoluteValue l E F i x
  exact hi.continuous

/-- Postcompose continuous field-valued functions by the actual coefficient embedding. -/
def rationalBalancedCoefficient (X : Scheme.{u}) :
    rationalCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X F := by
  letI := coefficientExtensionNormedField l E
  letI := coefficientExtensionNormedField l F
  exact continuousCoefficientMap
    (RingHom.ulift i.toRingHom : ULift.{u + 1} E →+* ULift.{u + 1} F)
    (continuous_uliftUp.comp
      ((rationalBalancedEmbedding_continuous l E F i).comp continuous_uliftDown)) X

private theorem rationalBalancedConstant_value (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (a : E) (x : U.unop.left) :
    rationalCoefficientValue l E X U
      ((rationalModuleConstantMap l E X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a))) x = a := by
  let := coefficientExtensionNormedField l E
  let η : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)) ⟶
      (rationalCoefficientSheaf l X E).obj :=
    { app := fun _ ↦ CommRingCat.ofHom
        { toFun := fun b ↦ ContinuousMap.const _ b
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }
  have hc : toSheafify (ProEt.topology X) _ ≫ (rationalModuleConstantMap l E X).hom =
      η := toSheafify_sheafifyLift (ProEt.topology X) η _
  have hv := ConcreteCategory.congr_hom (congr_app hc U) (ULift.up a : ULift.{u + 1} E)
  exact congrArg (fun b ↦ rationalCoefficientValue l E X U b x) hv

/-- The localized map has the pointwise inclusion formula and preserves reciprocals.
The unit and inverse equations include empty site objects. -/
theorem rationalBalancedCoefficient_sections (X : Scheme.{u}) :
    (∀ (U : X.ProEtᵒᵖ) (b : (rationalCoefficientSheaf l X E).obj.obj U)
      (x : U.unop.left),
      rationalCoefficientValue l F X U
          ((rationalBalancedCoefficient l E F i X).hom.app U b) x =
        i (rationalCoefficientValue l E X U b x)) ∧
    (∀ U : X.ProEtᵒᵖ, (rationalBalancedCoefficient l E F i X).hom.app U 1 = 1) ∧
    (∀ (U : X.ProEtᵒᵖ) (a : E), a ≠ 0 →
      ((rationalBalancedCoefficient l E F i X).hom.app U
        ((rationalModuleConstantMap l E X).hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
              (ULift.up a)))) *
        ((rationalModuleConstantMap l F X).hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} F)))).app U
              (ULift.up (i a⁻¹)))) = 1) := by
  refine ⟨fun _ _ _ ↦ rfl,
    fun U ↦ ((rationalBalancedCoefficient l E F i X).hom.app U).hom.map_one, ?_⟩
  intro U a ha
  let := coefficientExtensionNormedField l F
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change i (rationalCoefficientValue l E X U
      ((rationalModuleConstantMap l E X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a))) x) *
    rationalCoefficientValue l F X U
      ((rationalModuleConstantMap l F X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} F)))).app U
            (ULift.up (i a⁻¹)))) x = 1
  rw [rationalBalancedConstant_value, rationalBalancedConstant_value,
    ← map_mul, mul_inv_cancel₀ ha, map_one]

variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
variable (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)

private theorem rationalBalancedFiniteScalarsUnit
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (W : Scheme.{u}) (n : ℕ) :
    pbcFunctionScalars W d n = Functor.whiskerRight
      (toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
        (pbcLevelConstantComparison W d n).hom.hom)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let e := AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)
  have he : Functor.whiskerRight (toSheafify (ProEt.topology W)
        (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ e.hom.hom =
        AdicCoefficients.finiteRingUnit W (ProEtale.PbcQuotient d n) :=
    (AdicCoefficients.finiteRingComparison_exists W
      (ProEtale.PbcQuotient d n)).choose_spec.1.2
  have hconst : toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
      (pbcLevelConstantComparison W d n).hom.hom =
        AdicCoefficients.constants W (ProEtale.PbcQuotient d n) ≫
          toSheafify (ProEt.topology W)
            (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)) := by
    ext U b
    exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b
  rw [hconst]
  apply (cancel_mono e.hom.hom).1
  have hi : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg
    (fun f : AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ⟶
      AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ↦ f.hom)
    e.inv_hom_id
  change (ProEtale.finiteCoefficientScalarMap W (ProEtale.PbcQuotient d n) ≫
    e.inv.hom) ≫ e.hom.hom = _
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  rw [Functor.whiskerRight_comp, Category.assoc, he]
  rfl

private theorem rationalBalancedFiniteComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))]
    (s : RationalModuleRealization l E W) (n : ℕ) :
    letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        (s.finiteIso n).hom =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom ≫
        continuousCoefficientConstantComparison W (finiteCoefficientRing l E n) := by
  let _ : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let _ : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteContinuousCoefficientSheaf l W E n).property
  have hu := rationalBalancedFiniteScalarsUnit (pbcIntegralDatum l E) W n
  ext V a
  apply ContinuousMap.ext
  intro x
  have hn := s.finite_normalization n V a x
  have hunit := congrArg (fun z ↦ (z.app V).hom a) hu
  change _ = _ at hunit
  rw [hunit] at hn
  have hmap := congr_app (toSheafify_naturality (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).map (integralCoefficientULift l E n).toCommRingCatIso.hom)) V
  have hmap' := ConcreteCategory.congr_hom hmap a
  have hc := continuousCoefficientConstantComparison_unit W (finiteCoefficientRing l E n)
  have hc' := ConcreteCategory.congr_hom (congr_app hc V)
    (integralCoefficientULift l E n a)
  let e := (integralCoefficientULift l E n).toCommRingCatIso.hom
  let η := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)))
  let η' := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))
  let q := continuousCoefficientConstantComparison W (finiteCoefficientRing l E n)
  let m := sheafifyMap (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).map e)
  change (η'.app V) (e a) = (m.app V) ((η.app V) a) at hmap'
  change (q.hom.app V) ((η'.app V) (e a)) = ContinuousMap.const V.unop.left
    (show finiteCoefficientRing l E n from e a) at hc'
  let f : C(V.unop.left, finiteCoefficientRing l E n) :=
    (s.finiteIso n).hom.hom.app V
      ((pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom.hom.app V
        ((η.app V) a))
  change f x = e a at hn
  let g : C(V.unop.left, finiteCoefficientRing l E n) :=
    q.hom.app V ((m.app V) ((η.app V) a))
  change f x = g x
  rw [hn]
  have hg : g = ContinuousMap.const V.unop.left
      (show finiteCoefficientRing l E n from e a) := by
    change (q.hom.app V) ((m.app V) ((η.app V) a)) = _
    rw [← hmap']
    exact hc'
  exact (congrArg (fun z : C(V.unop.left, finiteCoefficientRing l E n) ↦ z x) hg).symm

private theorem rationalBalancedFiniteScalarChart (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    (AE : RationalModuleRealization l E W)
    (AF : RationalModuleRealization l F W) (n : ℕ) :
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    let : TopologicalSpace (finiteCoefficientRing l F n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l F n) := ⟨rfl⟩
    let q : finiteCoefficientRing l E n →+* finiteCoefficientRing l F n :=
      (integralCoefficientULift l F n).toRingHom.comp
      ((pbcScalarQuotientMap l E F i n).comp
        (integralCoefficientULift l E n).symm.toRingHom)
    AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) ≫
        (AF.finiteIso n).hom =
      (AE.finiteIso n).hom ≫ continuousCoefficientMap q continuous_of_discreteTopology W := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  let : TopologicalSpace (finiteCoefficientRing l F n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l F n) := ⟨rfl⟩
  let q : finiteCoefficientRing l E n →+* finiteCoefficientRing l F n :=
      (integralCoefficientULift l F n).toRingHom.comp
    ((pbcScalarQuotientMap l E F i n).comp
      (integralCoefficientULift l E n).symm.toRingHom)
  apply (cancel_epi (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).mp
  have hn :
      (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (pbcScalarQuotientMap l E F i n)) ≫
        (pbcLevelConstantComparison W (pbcIntegralDatum l F) n).hom := by
    exact (scalarLevelConstantComparison_naturality W (pbcIntegralDatum l E)
      (pbcIntegralDatum l F) n (pbcScalarQuotientMap l E F i n)).symm
  conv_lhs =>
    erw [← Category.assoc, hn, Category.assoc, rationalBalancedFiniteComparison l F W AF n]
  conv_rhs =>
    erw [← Category.assoc, rationalBalancedFiniteComparison l E W AE n, Category.assoc]
  erw [← discreteConstantComparison_naturality W (CommRingCat.ofHom q)]
  have hm : CommRingCat.ofHom (pbcScalarQuotientMap l E F i n) ≫
        (integralCoefficientULift l F n).toCommRingCatIso.hom =
      (integralCoefficientULift l E n).toCommRingCatIso.hom ≫ CommRingCat.ofHom q := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (integralCoefficientULift l E n).symm_apply_apply a |>.symm
      |> congrArg (fun a ↦ integralCoefficientULift l F n
        (pbcScalarQuotientMap l E F i n a))
  conv_lhs => erw [← Category.assoc, ← Functor.map_comp]
  conv_rhs => erw [← Category.assoc, ← Functor.map_comp]
  erw [hm]

/-- Integral coefficient inclusion is postcomposition under the specified realizations. -/
theorem rationalBalancedIntegralNormalization
    (U : X.ProEtᵒᵖ) (b : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left) :
    (integralCoefficientValue l F X U
      ((sE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i X ≫ sF.integralIso.hom).hom.app
        U b) x).val = i (integralCoefficientValue l E X U b x).val := by
  let c := sE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i X ≫ sF.integralIso.hom
  let q (n : ℕ) : finiteCoefficientRing l E n →+* finiteCoefficientRing l F n :=
    (integralCoefficientULift l F n).toRingHom.comp
    ((pbcScalarQuotientMap l E F i n).comp
      (integralCoefficientULift l E n).symm.toRingHom)
  have hq (n : ℕ) (a : Padic.coefficientExtensionIntegers l E) :
      q n (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) =
        ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))
          (WeilConjectures.integralScalarIntegerInclusion l E F i a)) := by
    change integralCoefficientULift l F n
      (pbcScalarQuotientMap l E F i n ((integralCoefficientULift l E n).symm _)) = _
    have hE : integralCoefficientULift l E n
        (Ideal.Quotient.mk _ (ULift.up a)) =
          ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) :=
      (integralCoefficientULift_exists l E n).exists.choose_spec (ULift.up a)
    rw [← hE, RingEquiv.symm_apply_apply]
    change integralCoefficientULift l F n
      (Ideal.Quotient.mk _ (pbcEmbeddingIntegerMap l E F i (ULift.up a))) = _
    exact (integralCoefficientULift_exists l F n).exists.choose_spec _
  have hres (n : ℕ) :
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))
          (integralCoefficientValue l F X U (c.hom.app U b) x) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))
          (WeilConjectures.integralScalarIntegerInclusion l E F i
            (integralCoefficientValue l E X U b x)) := by
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    let : TopologicalSpace (finiteCoefficientRing l F n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l F n) := ⟨rfl⟩
    have hs : c ≫ sF.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l F) n ≫
          (sF.finiteIso n).hom =
        (sE.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
          (sE.finiteIso n).hom) ≫ continuousCoefficientMap (q n)
            continuous_of_discreteTopology X := by
      simp only [c, Category.assoc, Iso.hom_inv_id_assoc]
      have hp : pbcScalarCoefficientMap l E F i X ≫
          pbcAdicProjection X (pbcIntegralDatum l F) n =
          pbcAdicProjection X (pbcIntegralDatum l E) n ≫
            AdicCoefficients.coefficientMap X (pbcScalarQuotientMap l E F i n) :=
        (pbcScalarCoefficientMap_exists l E F i X).exists.choose_spec n
      rw [reassoc_of% hp]
      erw [rationalBalancedFiniteScalarChart l E F i X sE sF n]
    have hv := congrArg (fun z ↦
      (finiteContinuousCoefficientValue l F X n U (z.hom.app U b) x).down) hs
    have he := sE.integral_normalization n U b x
    have hf := sF.integral_normalization n U (c.hom.app U b) x
    rw [← hf]
    change (finiteContinuousCoefficientValue l F X n U
      ((c ≫ sF.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l F) n ≫
        (sF.finiteIso n).hom).hom.app U b) x).down = _
    rw [hv]
    change (q n (finiteContinuousCoefficientValue l E X n U
      ((sE.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        (sE.finiteIso n).hom).hom.app U b) x)).down = _
    rw [← ULift.up_down (finiteContinuousCoefficientValue l E X n U
      ((sE.integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        (sE.finiteIso n).hom).hom.app U b) x), he, hq]
  obtain ⟨⟨e, he, _⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l F
  have h : integralCoefficientValue l F X U (c.hom.app U b) x =
      WeilConjectures.integralScalarIntegerInclusion l E F i
        (integralCoefficientValue l E X U b x) := by
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    exact hres n
  exact congrArg Subtype.val h

/-- The specific completed integral map localizes to continuous postcomposition. -/
theorem rationalBalancedCoefficient_square :
    pbcScalarCoefficientMap l E F i X ≫ (sF.integralIso.hom ≫ sF.inclusion) =
      (sE.integralIso.hom ≫ sE.inclusion) ≫ rationalBalancedCoefficient l E F i X := by
  apply (cancel_epi sE.integralIso.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply Sheaf.hom_ext
  ext U b
  apply rationalCoefficientValue_ext l F X U
  intro x
  change rationalCoefficientValue l F X U
      (sF.inclusion.hom.app U
        ((sE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i X ≫
          sF.integralIso.hom).hom.app U b)) x =
    i (rationalCoefficientValue l E X U (sE.inclusion.hom.app U b) x)
  exact (sF.inclusion_normalization U.unop _ x).trans
    ((rationalBalancedIntegralNormalization l E F i X sE sF U b x).trans
      (congrArg i (sE.inclusion_normalization U.unop b x)).symm)

/-- The s comparison, with common target F_X tensor over B_E,X. -/
def rationalBalancedS (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :=
  pbcReductionNormalization (pbcScalarCoefficientMap l E F i X)
    (sF.integralIso.hom ≫ sF.inclusion)
    ((sE.integralIso.hom ≫ sE.inclusion) ≫ rationalBalancedCoefficient l E F i X)
    (rationalBalancedCoefficient_square l E F i X sE sF) K

/-- The t comparison to the same single derived tensor. -/
def rationalBalancedT (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :=
  pbcReductionNormalization (sE.integralIso.hom ≫ sE.inclusion)
    (rationalBalancedCoefficient l E F i X)
    ((sE.integralIso.hom ≫ sE.inclusion) ≫ rationalBalancedCoefficient l E F i X) rfl K

/-- The component s followed by t inverse, transported by the recorded J object equations. -/
def rationalBalancedComponent
    (K : PbcRationalDerivedCategory l E X Fact.out Fact.out) :
    sF.J.obj ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) ≅
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).obj (sE.J.obj K) :=
  eqToIso (sF.objects ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj K.obj)) ≪≫
    rationalBalancedS l E F i X sE sF K.obj.obj ≪≫
    (rationalBalancedT l E F i X sE K.obj.obj).symm ≪≫
    (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).mapIso
      (eqToIso (sE.objects K.obj)).symm

/-- The specified components are natural for every raw fraction morphism. -/
theorem rationalBalancedComponent_naturality
    {K L : PbcRationalDerivedCategory l E X Fact.out Fact.out} (f : K ⟶ L) :
    (pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J).map f ≫
        (rationalBalancedComponent l E F i X sE sF L).hom =
      (rationalBalancedComponent l E F i X sE sF K).hom ≫
        (sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map f := by
  sorry

/-- The natural isomorphism on raw rationalizations, with its actual inverse components. -/
def rationalBalancedTheta :
    pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J ≅
      sE.J ⋙ pbcDerivedExtend (rationalBalancedCoefficient l E F i X) :=
  NatIso.ofComponents (rationalBalancedComponent l E F i X sE sF)
    (rationalBalancedComponent_naturality l E F i X sE sF)

section TensorModels
variable {W : Scheme.{u}}
  {R S B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
  (a : R ⟶ S) (b : S ⟶ B)

end TensorModels

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G) (sG : RationalModuleRealization l G X)

set_option linter.unusedSectionVars false in
/-- Continuous postcomposition composes as the given field embeddings do. -/
theorem rationalBalancedCoefficient_comp :
    rationalBalancedCoefficient l E F i X ≫ rationalBalancedCoefficient l F G j X =
      rationalBalancedCoefficient l E G (j.comp i) X := by
  ext U b
  rfl

/-- Successive theta comparisons agree with the specified direct raw associator.
This is an equation on the raw categories, so includes every fractional arrow. -/
theorem rationalBalancedTower
    (K : PbcRationalDerivedCategory l E X Fact.out Fact.out) :
    sG.J.map ((pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app K) ≫
        (rationalBalancedTheta l E G (j.comp i) X sE sG).hom.app K =
      (rationalBalancedTheta l F G j X sF sG).hom.app
          ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map
          ((rationalBalancedTheta l E F i X sE sF).hom.app K) ≫
        (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
          (rationalBalancedCoefficient l F G j X)
          (rationalBalancedCoefficient l E G (j.comp i) X)
          (rationalBalancedCoefficient_comp l E F i X G j) (sE.J.obj K)).hom := by
  sorry

variable (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
  (k : G →ₐ[ℚ_[l]] H)

attribute [-instance] ULift.module in
/-- Equality coefficients have the multiplication unitor, with its cochain computation.
Conjugation by the raw tensor unit makes the raw source functor literally id. -/
theorem rationalBalancedIdentity :
    rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X = 𝟙 _ ∧
    ∃ (o : pbcExtend (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X) ≅ 𝟭 _)
      (d : pbcDerivedExtend (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X) ≅ 𝟭 _),
      (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (U : X.ProEtᵒᵖ)
        (a : (rationalCoefficientSheaf l X E).obj.obj U) (m : M.val.obj U),
        (o.hom.app M).val.app U
            (pbcTensorSection (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X)
              M U a m) = a • m) ∧
      (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
        d.hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (rationalBalancedCoefficient l E E (AlgHom.id ℚ_[l] E) X) P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P)) ∧
      (∀ K : PbcRationalDerivedCategory l E X Fact.out Fact.out,
        (rationalBalancedTheta l E E (AlgHom.id ℚ_[l] E) X sE sE).hom.app K ≫
            d.hom.app (sE.J.obj K) =
          sE.J.map ((pbcRationalScalarUnit l E X Fact.out Fact.out).hom.app K)) := by
  sorry

section GeometricCoefficients
variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

variable [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

end GeometricCoefficients

/-- The s and t composition comparisons are natural on the entire derived category. -/
theorem rationalBalancedDerivedNaturality {W : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    {K L : DerivedCategory (pbcModules W R)} (f : K ⟶ L) :
    (pbcDerivedExtend b).map ((pbcDerivedExtend a).map f) ≫
        (pbcReductionNormalization a b c h L).hom =
      (pbcReductionNormalization a b c h K).hom ≫ (pbcDerivedExtend c).map f := by
  let e := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
    (pbcDerivedRestrictComp a b c h)
  have he (M : DerivedCategory (pbcModules W R)) :
      (pbcReductionNormalization a b c h M).hom = e.hom.app M := by
    dsimp [pbcReductionNormalization, pbcReductionNormalizationHom,
      pbcReductionTransition, e]
    simp only [Adjunction.leftAdjointCompIso_hom_app,
      Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [he, he]
  exact e.hom.naturality f

section
attribute [local irreducible] pbcRationalScalarExtension pbcScalarCoefficientMap

end

end AlgebraicGeometry.Scheme
