import Langlands.Representation.Plancherel.DiscreteSeriesFormalDegree

/-!
# Haar rescaling of the actual Schur formal degree

Multiplying the measure on the fixed central quotient by a positive scalar
preserves square-integrability and divides the actual formal degree by that
scalar. The canonical discrete-series classes are transported without changing
their underlying smooth isomorphism classes.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.Plancherel

open Langlands.HarishChandraSchwartz

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}

local instance scaledHaar [IsTopologicalGroup G] (c : ℝ≥0) [NeZero c] :
    (c • μ).IsHaarMeasure :=
  Measure.IsHaarMeasure.nnreal_smul μ (NeZero.ne c)

local instance scaledInv [IsTopologicalGroup G] [μ.IsInvInvariant] (c : ℝ≥0) :
    (c • μ).IsInvInvariant where
  inv_eq_self := by
    change Measure.map Inv.inv ((c : ℝ≥0∞) • μ) = (c : ℝ≥0∞) • μ
    rw [Measure.map_smul, Measure.map_inv_eq_self]
    exact measurable_inv.aemeasurable

omit [A.Normal] [BorelSpace (G ⧸ A)] [μ.IsHaarMeasure] in
/-- The two-representation crossed coefficient integral scales with the
actual measure. No integrability or nonzero-scalar premise is needed. -/
theorem orthogonalityIntegral_smul_measure
    {χ : A →* ℂˣ}
    (hρ : ∀ (a : A) (v : V), ρ a v = (χ a : ℂ) • v)
    (hσ : ∀ (a : A) (w : W), σ a w = (χ a : ℂ) • w)
    (c : ℝ≥0) (v₁ : V) (ℓ₁ : SmoothDual ρ) (w₂ : W) (ℓ₂ : SmoothDual σ) :
    orthogonalityIntegral A (c • μ) hρ hσ v₁ ℓ₁ w₂ ℓ₂ =
      ((c : ℝ) : ℂ) * orthogonalityIntegral A μ hρ hσ v₁ ℓ₁ w₂ ℓ₂ := by
  unfold orthogonalityIntegral
  rw [integral_smul_nnreal_measure]
  change (c : ℝ) • (_ : ℂ) = _
  rw [Complex.real_smul]

section Classes

variable [IsTopologicalGroup G]

/-- The same full-central-character witness works after rescaling the
measure, and inverse rescaling gives the converse. -/
theorem isSquareIntegrableModCentralSubgroup_smul_measure_iff
    (c : ℝ≥0) [NeZero c] :
    IsSquareIntegrableModCentralSubgroup A hA ρ (c • μ) ↔
      IsSquareIntegrableModCentralSubgroup A hA ρ μ := by
  constructor
  · rintro ⟨hadm, χ, hχ⟩
    refine ⟨hadm, χ, ?_⟩
    intro ℓ v
    have h := (hχ ℓ v).smul_measure (c := ((c⁻¹ : ℝ≥0) : ℝ≥0∞)) ENNReal.coe_ne_top
    change MemLp _ 2 (c⁻¹ • (c • μ)) at h
    simpa only [smul_smul, inv_mul_cancel₀ (NeZero.ne c), one_smul] using h
  · rintro ⟨hadm, χ, hχ⟩
    exact ⟨hadm, χ, fun ℓ v => (hχ ℓ v).smul_measure ENNReal.coe_ne_top⟩

/-- Rescaling preserves exactly the existing discrete-series predicate on
the canonical smooth dual. -/
theorem isDiscreteSeriesClass_smul_measure_iff
    (c : ℝ≥0) [NeZero c]
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    IsDiscreteSeriesClass A hA (c • μ) ω ↔ IsDiscreteSeriesClass A hA μ ω := by
  induction ω using Quotient.inductionOn with
  | h π => exact isSquareIntegrableModCentralSubgroup_smul_measure_iff A hA μ c

/-- The identity on underlying smooth isomorphism classes, between the
existing discrete-series subtypes for the two Haar normalizations. -/
def discreteSeriesClassHaarScalingEquiv (c : ℝ≥0) [NeZero c] :
    DiscreteSeriesClass.{uG, uV} A hA μ ≃ DiscreteSeriesClass.{uG, uV} A hA (c • μ) where
  toFun ω := ⟨ω.val, (isDiscreteSeriesClass_smul_measure_iff A hA μ c ω.val).mpr ω.property⟩
  invFun ω := ⟨ω.val, (isDiscreteSeriesClass_smul_measure_iff A hA μ c ω.val).mp ω.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem discreteSeriesClassHaarScalingEquiv_val
    (c : ℝ≥0) [NeZero c] (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    (discreteSeriesClassHaarScalingEquiv A hA μ c ω).val = ω.val :=
  rfl

@[simp]
theorem discreteSeriesClassHaarScalingEquiv_mk
    (c : ℝ≥0) [NeZero c]
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ) :
    discreteSeriesClassHaarScalingEquiv A hA μ c (discreteSeriesClass A hA μ π hπ) =
      discreteSeriesClass A hA (c • μ) π
        ((isSquareIntegrableModCentralSubgroup_smul_measure_iff A hA μ c).mpr hπ) :=
  rfl

variable [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

/-- The degree for `c • μ` is the actual degree for `μ` divided by `c`. -/
theorem representationFormalDegree_smul_measure
    (c : ℝ≥0) [NeZero c]
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ρ μ) (hi : ρ.IsIrreducible) :
    representationFormalDegree A hA (c • μ) hcof
      ((isSquareIntegrableModCentralSubgroup_smul_measure_iff A hA μ c).mpr hsq) hi =
        (c : ℝ)⁻¹ * representationFormalDegree A hA μ hcof hsq hi := by
  let hsq' := (isSquareIntegrableModCentralSubgroup_smul_measure_iff A hA μ c).mpr hsq
  let χ := Classical.choose hsq.2
  let hρ : ∀ (a : A) (v : V), ρ a v =
      ((χ.character.comp (Subgroup.inclusion hA)) a : ℂ) • v :=
    fun a v => χ.acts (Subgroup.inclusion hA a) v
  apply formalDegree_unique A hA (c • μ) hρ hcof hsq' hi
    (orthogonalityIntegral_eq_representationFormalDegree A hA (c • μ) hcof hρ hsq' hi)
  intro v₁ ℓ₁ v₂ ℓ₂
  rw [orthogonalityIntegral_smul_measure,
    orthogonalityIntegral_eq_representationFormalDegree A hA μ hcof hρ hsq hi]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, mul_inv_rev, inv_inv]
  ring

/-- The comparison for the existing class degrees uses the canonical
identity transport, preserving every actual underlying representation. -/
theorem discreteSeriesFormalDegree_smul_measure
    (c : ℝ≥0) [NeZero c] (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesFormalDegree A hA (c • μ) hcof
      (discreteSeriesClassHaarScalingEquiv A hA μ c ω) =
        (c : ℝ)⁻¹ * discreteSeriesFormalDegree A hA μ hcof ω := by
  rcases ω with ⟨ω, hω⟩
  induction ω using Quotient.inductionOn with
  | h π =>
    change IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ at hω
    change discreteSeriesFormalDegree A hA (c • μ) hcof
      (discreteSeriesClass A hA (c • μ) π
        ((isSquareIntegrableModCentralSubgroup_smul_measure_iff A hA μ c).mpr hω)) =
      (c : ℝ)⁻¹ * discreteSeriesFormalDegree A hA μ hcof (discreteSeriesClass A hA μ π hω)
    rw [discreteSeriesFormalDegree_mk, discreteSeriesFormalDegree_mk]
    exact representationFormalDegree_smul_measure A hA μ hcof c hω π.property.1

end Classes

end Langlands.Plancherel
