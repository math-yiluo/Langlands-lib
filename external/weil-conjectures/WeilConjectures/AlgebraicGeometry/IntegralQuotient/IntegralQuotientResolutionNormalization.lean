/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.PrincipalIdealDomain
import all WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Actual integral finite-quotient resolutions

Level n denotes exponent n + 1. The ring objects, multiplication, cone and projection
are exactly those of IntegralQuotientCoefficients. The finite constant identifications
are pinned by the existing constant-function map, and the limit isomorphism is pinned
by all the actual projections. The module equivalence is the fixed section-action one.

## References

* Stacks Project, Tags 093M, 093J and 06YQ
* Stacks 00YV
* Stacks 093I
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open WeilConjectures AlgebraicGeometry.ProEtale.IntegralPresentation
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing reconstructed commutative section-ring sheaf of the integral object. -/
abbrev resolutionSectionRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T)
    (condensedRingObj (integral l E) T)

/-- Forgetting commutativity of the same section ring; no coefficient is replaced. -/
abbrev resolutionUnderlyingRing (T : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (resolutionSectionRing l E T)

/-- The finite section ring, reconstructed from the actual pulled-back quotient. -/
abbrev resolutionFiniteRing (T : Scheme.{u}) (n : ℕ) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T)
    (condensedRingObj (finite l E n) T)

/-- The recorded internal/section module equivalence, with its exact forward functor. -/
abbrev resolutionSectionEquivalence (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T)
    (condensedRingObj (integral l E) T)

/-- The constant integral ring in the universe of abelian sheaves on the small site. -/
abbrev resolutionConstantRing (T : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))

private theorem coefficient_noetherian :
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  infer_instance

private theorem uniformizer_ne_zero : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro hz
  rw [hz, Ideal.span_singleton_zero] at hgen
  exact h.2.2.2.2.2.2.2.2.2.1 hgen.symm

private theorem coefficient_exact (n : ℕ) :
    Function.Exact (fun a : Padic.coefficientExtensionIntegers l E ↦
      Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a)
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
  intro x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x ∈ Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ (n + 1) ↔ _
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, ha.symm⟩, fun ⟨a, ha⟩ ↦ ⟨a, ha.symm⟩⟩

private theorem point_zero (n : ℕ) : multiplicationPoint l E n ≫ reduction l E n = 0 := by
  let := spectralNorm.normedField (Padic l) E
  ext S a
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a.down x) = 0
  apply (coefficient_exact l E n _).2
  exact ⟨a.down x, rfl⟩

private theorem point_shortExact (n : ℕ) :
    (ShortComplex.mk (multiplicationPoint l E n) (reduction l E n)
      (point_zero l E n)).ShortExact := by
  let := spectralNorm.normedField (Padic l) E
  let S := ShortComplex.mk (multiplicationPoint l E n) (reduction l E n)
    (point_zero l E n)
  apply DerivedNakayama.shortExact_of_sectionwise
  intro T
  let S' := (S.map (sheafToPresheaf (coherentTopology Profinite.{u}) Ab)).map
    ((evaluation Profinite.{u}ᵒᵖ Ab).obj T)
  have hf : Function.Injective S'.f := by
    intro f g h
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    exact mul_left_cancel₀ (pow_ne_zero (n + 1) (uniformizer_ne_zero l E))
      (congrArg (fun f ↦ f.down t) h)
  have hg : Function.Surjective S'.g := by
    intro f
    let lift : Padic.coefficientExtensionRing l E (n + 1) →
        Padic.coefficientExtensionIntegers l E :=
      Function.surjInv Ideal.Quotient.mk_surjective
    refine ⟨ULift.up ⟨lift ∘ f.down, continuous_of_discreteTopology.comp f.down.continuous⟩,
      ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  have he : S'.Exact := by
    apply S'.ab_exact_iff.mpr
    intro f hf
    have hdiv : ∀ t : T.unop, (f.down t : E) ∈ Set.range
        (fun a : Padic.coefficientExtensionIntegers l E ↦
          (Padic.coefficientExtensionUniformizer l E : E) ^ (n + 1) * (a : E)) := by
      intro t
      have hft := congrArg (fun f ↦ f.down t) hf
      change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (f.down t) = 0 at hft
      obtain ⟨a, ha⟩ := (coefficient_exact l E n _).1 hft
      refine ⟨a, ?_⟩
      simpa using congrArg (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) ha
    have ht : Padic.coefficientExtensionIntegersTopology l E =
        TopologicalSpace.induced
          (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E))
          (@UniformSpace.toTopologicalSpace E
            (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace) :=
      congrArg (fun t : TopologicalSpace E ↦ TopologicalSpace.induced
        (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t)
        (DerivedNakayama.coefficientTopology l E)
    have hfcont := f.down.continuous
    change @Continuous _ _ _ (Padic.coefficientExtensionIntegersTopology l E) _ at hfcont
    rw [ht] at hfcont
    obtain ⟨g, hg, hgf, _⟩ := (Padic.continuous_uniformizer_division l E (n + 1)).2
      f.down hfcont hdiv
    rw [← ht] at hg
    refine ⟨ULift.up ⟨g, hg⟩, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    change Padic.coefficientExtensionUniformizer l E ^ (n + 1) * g t = f.down t
    exact Subtype.ext (by simpa using hgf t)
  have : Mono S'.f := (AddCommGrpCat.mono_iff_injective _).mpr hf
  have : Epi S'.g := (AddCommGrpCat.epi_iff_surjective _).mpr hg
  exact ⟨he⟩

private theorem resolution_shortExact (T : Scheme.{u}) (n : ℕ) :
    ∃ h : multiplication l E T n ≫ projection l E T n = 0,
      (ShortComplex.mk (multiplication l E T n) (projection l E T n) h).ShortExact := by
  have h : multiplication l E T n ≫ projection l E T n = 0 := by
    apply Mod.hom_ext
    change (upperStarFromPoint T).map (multiplicationPoint l E n) ≫
      (upperStarFromPoint T).map (reduction l E n) = 0
    rw [← Functor.map_comp, point_zero, Functor.map_zero]
  refine ⟨h, ?_⟩
  have : PreservesFiniteLimits (upperStarFromPoint T) := by
    let := DerivedNakayama.pointFiniteLimits.{u}
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint T) := by
    have : (upperStarFromPoint T).IsLeftAdjoint :=
      (pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).isLeftAdjoint
    infer_instance
  apply ShortExact.reflects_shortExact_of_faithful (Mod.forget _)
  exact (point_shortExact l E n).map_of_exact (upperStarFromPoint T)

private theorem actual_projection_back (X : Scheme.{u}) (n : ℕ)
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
    (j : sfbIntegralProfinite l E ≅ c.pt)
    (hq : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
      (j.hom ≫ c.π.app (op n)) x =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x)
    (e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X)
    (hn : ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E),
      (sfbIntegralFiniteRepresentation l E X a n).hom.app
          (op ((profiniteToProEtOf X).obj S))
        ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
          (op ((profiniteToProEtOf X).obj S))
          (e.hom.hom.app (op ((profiniteToProEtOf X).obj S))
            (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
              (op S) (ULift.up g.hom.hom)))) =
        ULift.up ((profiniteToProEtOf X).map (g ≫ j.hom ≫ c.π.app (op n)))) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    (upperStarFromPoint X).map
      (reduction l E n) ≫
      finiteBack X (Padic.coefficientExtensionRing l E (n + 1)) a =
    e.hom ≫ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (limit.π (integralCoefficientSheafSystem l E X) (op n)) := by
  let := spectralNorm.normedField (Padic l) E
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  apply point_hom_ext X
  intro S f
  change (finiteBack X (Padic.coefficientExtensionRing l E (n + 1)) a).hom.app _
    (((upperStarFromPoint X).map
      (reduction l E n)).hom.app _
        (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) f)) = _
  refine (congrArg ((finiteBack X
    (Padic.coefficientExtensionRing l E (n + 1)) a).hom.app
      (op ((profiniteToProEtOf X).obj S)))
        (point_unit_map X
          (reduction l E n) S f)).trans ?_
  refine (finiteBack_unit X (Padic.coefficientExtensionRing l E (n + 1)) a S _).trans ?_
  let g : S ⟶ sfbIntegralProfinite l E := ConcreteCategory.ofHom f.down
  have ht := hn S g
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let V := op ((profiniteToProEtOf X).obj S)
  let z := (reduction l E n).hom.app (op S) f
  let k := finiteFunction B S z.down
  apply ((finiteRepresentation X a B).app V).toEquiv.injective
  change (finiteRepresentation X a B).hom.app V
      (finiteRingSection X a B S k) = _
  have hk : finiteRingSection X a B S k =
      (finiteRepresentation X a B).inv.app V
        (ULift.up ((profiniteToProEtOf X).map k)) := rfl
  rw [hk, (finiteRepresentation X a B).inv_hom_id_app_apply]
  refine Eq.trans ?_ ht.symm
  apply congrArg ULift.up
  apply congrArg (fun k ↦ (profiniteToProEtOf X).map k)
  apply ConcreteCategory.hom_ext
  intro x
  change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (f.down x) =
      (g ≫ j.hom ≫ c.π.app (op n)) x
  exact (hq n (g x)).symm

private theorem actual_normalizedRingComparison (X : Scheme.{u}) :
    ∃ α : resolutionSectionRing l E X ≅
        completedIntegralCommRingSheafUnrestricted l E X,
      ∀ (n : ℕ) (e : FiniteDiscreteOrdinary.Encoding
        (Padic.coefficientExtensionRing l E (n + 1)) X),
        α.inv ≫ CondensedRing.sectionRingMap X (coefficientMap (reduction l E n) X) =
          completedIntegralCommRingProjectionUnrestricted l E X n ≫ e.ringIso.hom := by
  obtain ⟨a, c, j, hq, _, _, _, _, e, ⟨he, hei, hn⟩, _⟩ :=
    sfb_integral_coefficient_limit l E X
  let := he
  let := hei
  let : IsCommMonObj (sfbCompletedIntegersAb l E X) :=
    Sheaf.isCommMonObj_sheafCompose_obj (Scheme.ProEt.topology X)
      (completedIntegralCoefficientSheafUnrestricted l E X) (fun U a b ↦ by
        let := completedIntegralCoefficientCommRingUnrestricted l E X U
        exact mul_comm a b)
  let : IsCommMonObj (coefficientRing X (sfbCondensedIntegers l E)).X :=
    inferInstanceAs (IsCommMonObj (condensedRingObj (integral l E) X))
  let : IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (completedIntegralCommRingSheafUnrestricted l E X))) :=
    inferInstanceAs (IsCommMonObj (sfbCompletedIntegersAb l E X))
  obtain ⟨α, hα⟩ := sectionRingComparison X
    (completedIntegralCommRingSheafUnrestricted l E X) e
  refine ⟨α, fun n en ↦ ?_⟩
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  have hb := actual_projection_back l E X n a c j hq e (fun S g ↦ hn S g n)
  apply rotate_square α en.ringIso
  let F := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})
  apply F.map_injective
  rw [F.map_comp, F.map_comp, hα, finiteBack_ringIso X _ a en]
  exact hb

private def liftedPowerQuotient (A : Type u) [CommRing A] (a : A) (n : ℕ) :
    (ULift.{u + 1} A ⧸ (Ideal.span {ULift.up a}) ^ n) ≃+*
      ULift.{u + 1} (A ⧸ (Ideal.span {a}) ^ n) :=
  (Ideal.quotientEquiv _ _ ULift.ringEquiv (by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl)).trans ULift.ringEquiv.symm

private abbrev liftedIdeal := Ideal.span
  ({ULift.up (Padic.coefficientExtensionUniformizer l E)} :
    Set (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))

private def finiteCompletionIso (T : Scheme.{u}) (n : ℕ) :
    (Scheme.adicLisseForget T).obj
      ((Scheme.adicLisseRingSystem T (liftedIdeal l E)).obj (op n)) ≅
        integralCoefficientSheaf l E T n :=
  (Scheme.adicLisseForget T).mapIso
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).mapIso
      (RingEquiv.toCommRingCatIso (liftedPowerQuotient
        (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E) (n + 1))))

private theorem finiteCompletionIso_naturality (T : Scheme.{u}) (n : ℕ) :
    ((Scheme.adicLisseRingSystem T (liftedIdeal l E)) ⋙ Scheme.adicLisseForget T).map
      (homOfLE (Nat.le_succ n)).op ≫ (finiteCompletionIso l E T n).hom =
        (finiteCompletionIso l E T (n + 1)).hom ≫
          integralCoefficientSheafTransition l E T n := by
  simp only [Functor.comp_map, Scheme.adicLisseRingSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  change (Scheme.adicLisseForget T).map
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc (liftedIdeal l E) (n + 1)))) ≫ _ = _
  unfold finiteCompletionIso integralCoefficientSheafTransition
  simp only [Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  ext x
  rfl

private def completionTowerIso (T : Scheme.{u}) :
    Scheme.adicLisseRingSystem T (liftedIdeal l E) ⋙ Scheme.adicLisseForget T ≅
      integralCoefficientSheafSystem l E T := by
  let f : Scheme.adicLisseRingSystem T (liftedIdeal l E) ⋙ Scheme.adicLisseForget T ⟶
      integralCoefficientSheafSystem l E T :=
    NatTrans.ofOpSequence (fun n ↦ (finiteCompletionIso l E T n).hom)
      (fun n ↦ by
        simpa only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
          using finiteCompletionIso_naturality l E T n)
  have : ∀ n, IsIso (f.app n) := fun n ↦ by
    change IsIso (finiteCompletionIso l E T n.unop).hom
    infer_instance
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact asIso f

private def completionRingIso (T : Scheme.{u}) :
    (Scheme.adicLisseForget T).obj (Scheme.adicLisseCompletedRing T (liftedIdeal l E)) ≅
      completedIntegralCoefficientSheafUnrestricted l E T :=
  preservesLimitIso (Scheme.adicLisseForget T) (Scheme.adicLisseRingSystem T (liftedIdeal l E))
    ≪≫ lim.mapIso (completionTowerIso l E T)

private theorem completionRingIso_projection (T : Scheme.{u}) (n : ℕ) :
    (completionRingIso l E T).hom ≫
      limit.π (integralCoefficientSheafSystem l E T) (op n) =
        (Scheme.adicLisseForget T).map
          (limit.π (Scheme.adicLisseRingSystem T (liftedIdeal l E)) (op n)) ≫
            (finiteCompletionIso l E T n).hom := by
  unfold completionRingIso
  change ((preservesLimitIso _ _).hom ≫ lim.map (completionTowerIso l E T).hom) ≫ _ = _
  erw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]
  rfl

private theorem completion_scalar (T : Scheme.{u}) (n : ℕ) :
    (Scheme.adicLisseForget T).map
      ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk ((liftedIdeal l E) ^ (n + 1))))) ≫
          (finiteCompletionIso l E T n).hom =
            integralConstantQuotientOfUniverses l E T n := by
  unfold finiteCompletionIso integralConstantQuotientOfUniverses
  simp only [Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

private theorem completion_flat_unit (T : Scheme.{u})
    (α : resolutionSectionRing l E T ≅ completedIntegralCommRingSheafUnrestricted l E T) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T) (R := resolutionConstantRing l E T)
      ((SheafOfModules.restrictScalars
        (integralConstantToCompletionOfUniverses l E T ≫
          (Scheme.adicLisseForget T).map α.inv)).obj
            (SheafOfModules.unit (resolutionUnderlyingRing l E T))) := by
  let F := Scheme.adicLisseForget T
  let e : Scheme.adicLisseCompletedRing T (liftedIdeal l E) ≅
      resolutionSectionRing l E T :=
    F.preimageIso (completionRingIso l E T ≪≫ (F.mapIso α).symm)
  let c : resolutionConstantRing l E T ⟶ resolutionSectionRing l E T :=
    F.preimage (integralConstantToCompletionOfUniverses l E T ≫ F.map α.inv)
  have hc : ∀ n : ℕ,
      c ≫ e.inv ≫ limit.π (Scheme.adicLisseRingSystem T (liftedIdeal l E)) (op n) =
        (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk ((liftedIdeal l E) ^ (n + 1)))) := by
    intro n
    apply F.map_injective
    simp only [Functor.map_comp, c, Functor.map_preimage, e, Functor.preimageIso_inv,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom]
    apply (cancel_mono (finiteCompletionIso l E T n).hom).mp
    rw [completion_scalar]
    simp only [Category.assoc]
    rw [← completionRingIso_projection]
    simp only [← Category.assoc, ← F.map_comp, Iso.inv_hom_id, Category.id_comp]
    exact limit.lift_π (integralConstantConeOfUniverses l E T) (op n)
  let : IsNoetherianRing (Padic.coefficientExtensionIntegers l E) := coefficient_noetherian l E
  let : IsNoetherianRing (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
    isNoetherianRing_of_ringEquiv _ ULift.ringEquiv.symm
  have h := Scheme.CompletedConstantAlgebra.flat_presented_completion T
    (liftedIdeal l E) e c hc
  change SheafOfModules.IsFlatOnSite
    ((SheafOfModules.restrictScalars (F.map c)).obj (SheafOfModules.unit _)) at h
  simpa only [c, Functor.map_preimage] using h

private def regularSectionIso (T : Scheme.{u}) :
    (resolutionSectionEquivalence l E T).functor.obj
      (Mod.regular (condensedRingObj (integral l E) T)) ≅
        SheafOfModules.unit (resolutionUnderlyingRing l E T) := by
  unfold resolutionSectionEquivalence InternalAbelianSheafModule.sectionModuleEquivalence
  exact InternalAbelianSheafModule.comparison_unitIso
    (Scheme.ProEt.topology T) (condensedRingObj (integral l E) T)

private theorem completion_flat (T : Scheme.{u})
    (α : resolutionSectionRing l E T ≅ completedIntegralCommRingSheafUnrestricted l E T) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T) (R := resolutionConstantRing l E T)
      ((SheafOfModules.restrictScalars
        (integralConstantToCompletionOfUniverses l E T ≫
          (Scheme.adicLisseForget T).map α.inv)).obj
            ((resolutionSectionEquivalence l E T).functor.obj
              (Mod.regular (condensedRingObj (integral l E) T)))) := by
  let R := resolutionConstantRing l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let res := SheafOfModules.restrictScalars
    (integralConstantToCompletionOfUniverses l E T ≫ (Scheme.adicLisseForget T).map α.inv)
  have h := SheafOfModules.flat_to_cat R _ (completion_flat_unit l E T α)
  have h' := (ObjectProperty.flat.prop_iff_of_iso
    (res.mapIso (regularSectionIso l E T))).2 h
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm h'.2

private theorem cone_flat_terms {A : Type*} [Category A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] {P : A}
    (f : P ⟶ P) (hP : ObjectProperty.flat P) (i : ℤ) :
    ObjectProperty.flat ((CochainComplex.mappingCone
      ((CochainComplex.singleFunctor A 0).map f)).X i) := by
  have hs (j : ℤ) : ObjectProperty.flat
      (((CochainComplex.singleFunctor A 0).obj P).X j) := by
    by_cases hj : j = 0
    · subst j
      exact (ObjectProperty.flat.prop_iff_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P)).2 hP
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P j hj)
  by_cases hi : i = -1
  · subst i
    apply (ObjectProperty.flat.prop_iff_of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        ((CochainComplex.singleFunctor A 0).map f) (-1) 0 (by decide))).2
    exact (ObjectProperty.flat.prop_iff_of_iso (isoBiprodZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P (-1) (by decide)))).1 (hs 0)
  · by_cases hi' : i = 0
    · subst i
      apply (ObjectProperty.flat.prop_iff_of_iso
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          ((CochainComplex.singleFunctor A 0).map f) 0 1 (by decide))).2
      exact (ObjectProperty.flat.prop_iff_of_iso (isoZeroBiprod
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P 1 (by decide)))).1 (hs 0)
    · exact ObjectProperty.flat_of_isZero ((CochainComplex.mappingCone.isZero_X_iff _ i).2
        ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P (i + 1) (by omega),
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P i hi'⟩)

private theorem cone_bounds {A : Type*} [Category A] [Abelian A] {P : A} (f : P ⟶ P) :
    (CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map f)).IsStrictlyGE (-1) ∧
      (CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map f)).IsStrictlyLE 0 := by
  constructor
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff _ i).2
      ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P (i + 1) (by omega),
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P i (by omega)⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff _ i).2
      ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P (i + 1) (by omega),
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P i (by omega)⟩

private theorem cone_augmentation {A : Type*} [Category A] [Abelian A]
    [HasZeroObject A] [HasBinaryBiproducts A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ ε : CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map S.f) ⟶
        (CochainComplex.singleFunctor A 0).obj S.X₃,
      CochainComplex.mappingCone.inr ((CochainComplex.singleFunctor A 0).map S.f) ≫ ε =
        (CochainComplex.singleFunctor A 0).map S.g ∧ QuasiIso ε := by
  have : PreservesFiniteLimits (CochainComplex.singleFunctor A 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single A (.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor A 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single A (.up ℤ) 0))
  exact ⟨CochainComplex.mappingCone.descShortComplex (S.map
      (CochainComplex.singleFunctor A 0)),
    CochainComplex.mappingCone.inr_descShortComplex
      (S.map (CochainComplex.singleFunctor A 0)),
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (hS.map_of_exact (CochainComplex.singleFunctor A 0))⟩

private theorem equivalence_quasiIso {A B : Type*} [Category A] [Abelian A]
    [Category B] [Abelian B] (e : A ≌ B) [e.functor.Additive]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((e.functor.mapHomologicalComplex (.up ℤ)).map f) :=
  HomologicalComplex.quasiIso_map_of_preservesHomology f e.functor

private theorem section_flat (T : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integral l E) T))
    (h : exactFunctor _ _ (tensorRight M)) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T) (R := resolutionSectionRing l E T)
      ((resolutionSectionEquivalence l E T).functor.obj M) :=
  (InternalAbelianSheafModule.comparison_flat
    (Scheme.ProEt.topology T) (condensedRingObj (integral l E) T) M).1 h

attribute [local irreducible] InternalAbelianSheafModule.comparison_closed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  InternalAbelianSheafModule.sectionModuleEquivalence multiplication projection

/-- Arithmetic, the canonically normalized limit presentation, flatness over constant
integral scalars, the actual cokernel, and the normalized flat-term K-flat resolution.
All assertions use the ordinary module categories and their unbounded complexes.
-/
theorem integral_quotient_resolution_normalization :
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    (∀ n : ℕ,
      Padic.coefficientExtensionUniformizer l E ^ (n + 1) ≠ 0 ∧
      Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
      Function.Injective (fun a : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a) ∧
      Function.Exact (fun a : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a)
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
      Function.Surjective
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))) ∧
    ∀ T : Scheme.{u},
      ∃ (α : resolutionUnderlyingRing l E T ≅
          WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T)
        (c : ∀ n : ℕ,
          (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (resolutionFiniteRing l E T n) ≅
            WeilConjectures.integralCoefficientSheaf l E T n),
        (∀ (n : ℕ) (U : T.ProEtᵒᵖ)
            (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))),
          (c n).inv.hom.app U
              ((toSheafify (Scheme.ProEt.topology T)
                ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U a) =
            (FiniteDiscreteOrdinary.canonicalAbelianMap
              (Padic.coefficientExtensionRing l E (n + 1)) T).hom.app U
                ((toSheafify (Scheme.ProEt.topology T)
                  ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of
                    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
                      U a)) ∧
        (∀ n : ℕ,
          α.hom ≫ limit.π (WeilConjectures.integralCoefficientSheafSystem l E T) (op n) =
            (sheafCompose (Scheme.ProEt.topology T)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
                  (Scheme.ProEt.topology T)
                  (coefficientMap (reduction l E n) T)) ≫ (c n).hom) ∧
        SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
          (R := resolutionConstantRing l E T)
          ((SheafOfModules.restrictScalars
            (WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫ α.inv)).obj
              ((resolutionSectionEquivalence l E T).functor.obj
                (Mod.regular (condensedRingObj (integral l E) T)))) ∧
        ∀ n : ℕ,
          Mono (multiplication l E T n) ∧
          (∃ h : multiplication l E T n ≫ projection l E T n = 0,
            Nonempty (IsColimit (CokernelCofork.ofπ (projection l E T n) h)) ∧
            ((ShortComplex.mk (multiplication l E T n) (projection l E T n) h).map
              (resolutionSectionEquivalence l E T).functor).ShortExact) ∧
          (∀ i : ℤ, exactFunctor _ _ (tensorRight ((resolution l E T n).X i))) ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (resolution l E T n) ∧
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite
            (J := Scheme.ProEt.topology T) (R := resolutionSectionRing l E T)
            ((resolutionSectionEquivalence l E T).functor.obj ((resolution l E T n).X i))) ∧
          CochainComplex.IsKFlatIndependentCoefficients
            (((resolutionSectionEquivalence l E T).functor.mapHomologicalComplex
              (.up ℤ)).obj (resolution l E T n)) ∧
          ∃ ε : resolution l E T n ⟶
              (CochainComplex.singleFunctor _ 0).obj
                ((Mod.comap (coefficientMap (reduction l E n) T)).obj
                  (Mod.regular (condensedRingObj (finite l E n) T))),
            CochainComplex.mappingCone.inr
                ((CochainComplex.singleFunctor _ 0).map (multiplication l E T n)) ≫ ε =
              (CochainComplex.singleFunctor _ 0).map (projection l E T n) ∧
            QuasiIso ε ∧
            QuasiIso (((resolutionSectionEquivalence l E T).functor.mapHomologicalComplex
              (.up ℤ)).map ε) := by
  classical
  refine ⟨coefficient_noetherian l E, ?_, ?_⟩
  · intro n
    have hz := pow_ne_zero (n + 1) (uniformizer_ne_zero l E)
    exact ⟨hz, Padic.finite_coefficientExtensionRing l E (n + 1) (by omega),
      mul_right_injective₀ hz, coefficient_exact l E n, Ideal.Quotient.mk_surjective⟩
  · intro T
    obtain ⟨α, hα⟩ := actual_normalizedRingComparison l E T
    let F := Scheme.adicLisseForget T
    let en (n : ℕ) : FiniteDiscreteOrdinary.Encoding
        (Padic.coefficientExtensionRing l E (n + 1)) T := by
      let := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
      exact (FiniteDiscreteOrdinary.encoding_exists
        (Padic.coefficientExtensionRing l E (n + 1)) T).some
    let αR := F.mapIso α
    let c (n : ℕ) := F.mapIso (en n).ringIso.symm
    refine ⟨αR, c, ?_, ?_, completion_flat l E T α, ?_⟩
    · intro n U a
      exact (en n).normalization U a
    · intro n
      have hh := congrArg F.map (hα n (en n))
      simp only [Functor.map_comp] at hh
      have hp : F.map (completedIntegralCommRingProjectionUnrestricted l E T n) =
          limit.π (integralCoefficientSheafSystem l E T) (op n) := by
        ext U x
        rfl
      have hq : F.map (CondensedRing.sectionRingMap T (coefficientMap (reduction l E n) T)) =
          F.map (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap (reduction l E n) T)) := by
        ext U x
        rfl
      rw [hp, hq] at hh
      change αR.inv ≫ _ = _ ≫ (c n).inv at hh
      apply (cancel_epi αR.inv).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using (congrArg (fun f ↦ f ≫ (c n).hom) hh).symm
    · intro n
      obtain ⟨hz, hs⟩ := resolution_shortExact l E T n
      let S := ShortComplex.mk (multiplication l E T n) (projection l E T n) hz
      have : Mono (multiplication l E T n) := hs.mono_f
      have : Epi (projection l E T n) := hs.epi_g
      have hq : IsColimit (CokernelCofork.ofπ (projection l E T n) hz) := hs.exact.gIsCokernel
      have hf (i : ℤ) : ObjectProperty.flat ((resolution l E T n).X i) :=
        cone_flat_terms (multiplication l E T n) (ObjectProperty.prop_unit _) i
      have hfs (i : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := Scheme.ProEt.topology T) (R := resolutionSectionRing l E T)
          ((resolutionSectionEquivalence l E T).functor.obj ((resolution l E T n).X i)) :=
        section_flat l E T _ (hf i).2
      have hb := cone_bounds (multiplication l E T n)
      have hge : (resolution l E T n).IsStrictlyGE (-1) := hb.1
      have hle : (resolution l E T n).IsStrictlyLE 0 := hb.2
      have hk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (resolution l E T n) := by
        exact CochainComplex.kFlat_of_bounded_of_flat (resolution l E T n) (-1) 0 hf
      have hks := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
        (resolutionSectionRing l E T)
        (((resolutionSectionEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj
          (resolution l E T n)) 0 hfs
      have hcone := cone_augmentation
        (A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (integral l E) T)) S hs
      obtain ⟨ε, haug, hε⟩ := hcone
      refine ⟨inferInstance, ⟨hz, ⟨hq⟩,
        hs.map_of_exact (resolutionSectionEquivalence l E T).functor⟩,
        (fun i ↦ (hf i).2), hk, hfs, hks, ε, ?_, hε, ?_⟩
      · exact haug
      · exact equivalence_quasiIso (resolutionSectionEquivalence l E T) ε

end AlgebraicGeometry.ProEtale.IntegralQuotient
