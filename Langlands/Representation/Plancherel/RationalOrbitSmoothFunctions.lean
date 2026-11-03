import Langlands.Representation.Plancherel.RationalOrbitIntegration
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Scalar smooth functions on actual discrete-series twist orbits -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal ContDiff CategoryTheory.MonObj BoundedContinuousFunction

namespace Langlands.Plancherel

/-- The usual real-angle covering of a finite product of unit circles. -/
def finiteTorusExp {J : Type*} (x : J → ℝ) : J → Circle :=
  fun i => Circle.exp (x i)

theorem isOpenQuotientMap_finiteTorusExp (J : Type*) :
    IsOpenQuotientMap (finiteTorusExp (J := J)) :=
  IsOpenQuotientMap.piMap fun _ =>
    ⟨Circle.exp_surjective, Circle.exp.continuous, isLocalHomeomorph_circleExp.isOpenMap⟩

@[simp]
theorem finiteTorusExp_add {J : Type*} (x y : J → ℝ) :
    finiteTorusExp (x + y) = finiteTorusExp x * finiteTorusExp y := by
  funext i
  exact Circle.exp_add _ _

/-- Real smoothness of a scalar torus function, tested on its real-angle lift.
This uses the standard exponential covering, without a choice of local charts. -/
def IsSmoothFiniteTorusFunction {J : Type*} [Fintype J] (f : (J → Circle) → ℂ) : Prop :=
  ContDiff ℝ ∞ (f ∘ finiteTorusExp)

theorem IsSmoothFiniteTorusFunction.continuous {J : Type*} [Fintype J]
    {f : (J → Circle) → ℂ} (hf : IsSmoothFiniteTorusFunction f) : Continuous f :=
  (isOpenQuotientMap_finiteTorusExp J).isQuotientMap.continuous_iff.mpr (ContDiff.continuous hf)

/-- Translating torus parameters preserves smoothness in both directions. -/
theorem isSmoothFiniteTorusFunction_mul_const_iff {J : Type*} [Fintype J]
    (f : (J → Circle) → ℂ) (c : J → Circle) :
    IsSmoothFiniteTorusFunction (fun z => f (z * c)) ↔ IsSmoothFiniteTorusFunction f := by
  obtain ⟨a, ha⟩ := (isOpenQuotientMap_finiteTorusExp J).surjective c
  subst c
  constructor
  · intro h
    have hh := h.comp (contDiff_id.sub contDiff_const :
      ContDiff ℝ ∞ (fun x : J → ℝ => x - a))
    simpa only [IsSmoothFiniteTorusFunction, Function.comp_def, ← finiteTorusExp_add, sub_add_cancel, id_eq] using hh
  · intro h
    have hh := h.comp (contDiff_id.add contDiff_const :
      ContDiff ℝ ∞ (fun x : J → ℝ => x + a))
    simpa only [IsSmoothFiniteTorusFunction, Function.comp_def, finiteTorusExp_add, id_eq] using hh

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalOrbitSmoothGroupPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalOrbitSmoothNonarchimedeanGroup :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
variable (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
variable (hG : GroupScheme.IsConnectedReductive G)

/-- Scalar smoothness on the actual orbit: pull back along its existing finite
circle coordinates and then the standard exponential covering. -/
def IsSmoothRationalOrbitFunction :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ) → Prop := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f
  exact IsSmoothFiniteTorusFunction
    (f ∘ rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega)

/-- Smoothness implies continuity for the actual quotient topology; continuity
is derived, rather than included in the definition. -/
theorem IsSmoothRationalOrbitFunction.continuous :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      {f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}
      (_hf : IsSmoothRationalOrbitFunction s hs mu hG omega f), Continuous f := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f hf
  exact (isOpenQuotientMap_rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega
    ).isQuotientMap.continuous_iff.mpr (IsSmoothFiniteTorusFunction.continuous hf)

/-- Changing the base representation inside its actual orbit preserves scalar
smoothness. In character coordinates the change is a torus translation. -/
theorem isSmoothRationalOrbitFunction_baseChange_iff :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
      (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ),
      IsSmoothRationalOrbitFunction s hs mu hG (chi • omega)
        (f ∘ discreteSeriesOrbitBaseChange (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega chi) ↔
        IsSmoothRationalOrbitFunction s hs mu hG omega f := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega chi f
  let e := rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG
  change IsSmoothFiniteTorusFunction
    ((f ∘ discreteSeriesOrbitBaseChange _ _ _ _ omega chi) ∘
      rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG (chi • omega)) ↔
    IsSmoothFiniteTorusFunction (f ∘ rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega)
  have hparam :
      (f ∘ discreteSeriesOrbitBaseChange _ _ _ _ omega chi) ∘
        rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG (chi • omega) =
      fun z => (f ∘ rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega) (z * e chi) := by
    funext z
    apply congrArg f
    apply Subtype.ext
    change e.symm z • (chi • omega) = e.symm (z * e chi) • omega
    rw [map_mul, e.symm_apply_apply, mul_smul]
  rw [hparam]
  exact isSmoothFiniteTorusFunction_mul_const_iff _ (e chi)

/-- The actual algebra of scalar smooth orbit functions, with pointwise
operations. It is not the coefficient-tensor space of VI.1. -/
def rationalSmoothOrbitFunctions :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      Subalgebra ℂ (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact
    { carrier := {f | IsSmoothRationalOrbitFunction s hs mu hG omega f}
      algebraMap_mem' := by
        intro c
        change ContDiff ℝ ∞ (fun _ => c)
        exact contDiff_const
      add_mem' := by
        intro f g hf hg
        change ContDiff ℝ ∞ _ at hf hg ⊢
        exact hf.add hg
      mul_mem' := by
        intro f g hf hg
        change ContDiff ℝ ∞ _ at hf hg ⊢
        exact hf.mul hg
      zero_mem' := by
        change ContDiff ℝ ∞ (fun _ => (0 : ℂ))
        exact contDiff_const
      one_mem' := by
        change ContDiff ℝ ∞ (fun _ => (1 : ℂ))
        exact contDiff_const }

/-- The actual inclusion of scalar smooth functions into bounded continuous
orbit functions, as a complex algebra homomorphism. -/
def rationalSmoothOrbitToBoundedContinuous :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      rationalSmoothOrbitFunctions s hs mu hG omega →ₐ[ℂ]
        (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
          (fun psi => (rationalNormCharacters G psi).toMul) omega →ᵇ ℂ) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  let := compactSpace_rationalDiscreteSeriesOrbit s hs mu omega
  exact
    { toFun := fun f => BoundedContinuousFunction.mkOfCompact
        ⟨f.val, IsSmoothRationalOrbitFunction.continuous s hs mu hG omega f.property⟩
      map_zero' := by ext; rfl
      map_one' := by ext; rfl
      map_add' := by intros; ext; rfl
      map_mul' := by intros; ext; rfl
      commutes' := by intro; ext; rfl }

@[simp]
theorem rationalSmoothOrbitToBoundedContinuous_apply :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (f : rationalSmoothOrbitFunctions s hs mu hG omega)
      (eta : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega),
      rationalSmoothOrbitToBoundedContinuous s hs mu hG omega f eta = f.val eta := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intros
  rfl

theorem rationalSmoothOrbitToBoundedContinuous_injective :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      Function.Injective (rationalSmoothOrbitToBoundedContinuous s hs mu hG omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f g hfg
  apply Subtype.ext
  funext eta
  exact congrArg (fun k => k eta) hfg

/-- Smooth scalar orbit functions have convergent integrals with the fixed
I.1/VI.3 character scale. -/
theorem IsSmoothRationalOrbitFunction.integrable [IsAffine T.X.left]
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      {f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}
      (_hf : IsSmoothRationalOrbitFunction s hs mu hG omega f),
      Integrable f (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f hf
  exact integrable_rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega
    (IsSmoothRationalOrbitFunction.continuous s hs mu hG omega hf)

end Langlands.Plancherel
