import Langlands.Representation.Plancherel.FormalDegreeHaarScaling

/-!
# Haar rescaling of the actual discrete-series twist orbits

The canonical identity transport of discrete-series classes commutes with the
existing unitary unramified twist action. It therefore transports the actual
orbit quotient, with the inverse-scaling law for the orbit formal degree.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.Plancherel

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

local instance orbitScaledHaar (c : ℝ≥0) [NeZero c] :
    (c • μ).IsHaarMeasure :=
  Measure.IsHaarMeasure.nnreal_smul μ (NeZero.ne c)

local instance orbitScaledInv [μ.IsInvInvariant] (c : ℝ≥0) :
    (c • μ).IsInvInvariant where
  inv_eq_self := by
    change Measure.map Inv.inv ((c : ℝ≥0∞) • μ) = (c : ℝ≥0∞) • μ
    rw [Measure.map_smul, Measure.map_inv_eq_self]
    exact measurable_inv.aemeasurable

/-- Changing only the quotient Haar scale commutes with the actual twist. -/
@[simp]
theorem discreteSeriesClassHaarScalingEquiv_smul
    (c : ℝ≥0) [NeZero c] (χ : unitaryUnramifiedCharacters ν)
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesClassHaarScalingEquiv A hA μ c (χ • ω) =
      χ • discreteSeriesClassHaarScalingEquiv A hA μ c ω := by
  apply Subtype.ext
  rfl

/-- The inverse class transport also commutes with the actual twist. -/
@[simp]
theorem discreteSeriesClassHaarScalingEquiv_symm_smul
    (c : ℝ≥0) [NeZero c] (χ : unitaryUnramifiedCharacters ν)
    (ω : DiscreteSeriesClass.{uG, uV} A hA (c • μ)) :
    (discreteSeriesClassHaarScalingEquiv A hA μ c).symm (χ • ω) =
      χ • (discreteSeriesClassHaarScalingEquiv A hA μ c).symm ω := by
  apply Subtype.ext
  rfl

/-- The actual orbit membership relation is unchanged by Haar rescaling. -/
theorem mem_discreteSeriesOrbit_haarScaling_iff
    (c : ℝ≥0) [NeZero c] (ω η : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesClassHaarScalingEquiv A hA μ c η ∈
        discreteSeriesOrbit A hA (c • μ) ν
          (discreteSeriesClassHaarScalingEquiv A hA μ c ω) ↔
      η ∈ discreteSeriesOrbit A hA μ ν ω := by
  rw [mem_discreteSeriesOrbit_iff, mem_discreteSeriesOrbit_iff]
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨χ, (discreteSeriesClassHaarScalingEquiv A hA μ c).injective ?_⟩
    rw [discreteSeriesClassHaarScalingEquiv_smul]
    exact hχ
  · rintro ⟨χ, rfl⟩
    exact ⟨χ, (discreteSeriesClassHaarScalingEquiv_smul A hA μ ν c χ ω).symm⟩

/-- The unitary twist stabilizer is unchanged; this asserts no finiteness. -/
theorem discreteSeriesStabilizer_haarScaling
    (c : ℝ≥0) [NeZero c] (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesStabilizer A hA (c • μ) ν
        (discreteSeriesClassHaarScalingEquiv A hA μ c ω) =
      discreteSeriesStabilizer A hA μ ν ω := by
  ext χ
  rw [mem_discreteSeriesStabilizer_iff, mem_discreteSeriesStabilizer_iff,
    ← discreteSeriesClassHaarScalingEquiv_smul]
  exact (discreteSeriesClassHaarScalingEquiv A hA μ c).injective.eq_iff

/-- Canonical transport of the existing actual unitary twist-orbit quotient. -/
def discreteSeriesOrbitHaarScalingEquiv (c : ℝ≥0) [NeZero c] :
    DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μ ν ≃
      DiscreteSeriesOrbitClass.{uG, uI, uV} A hA (c • μ) ν where
  toFun := Quotient.map (discreteSeriesClassHaarScalingEquiv A hA μ c)
    (by
      intro ω η h
      obtain ⟨χ, hχ⟩ := h
      refine ⟨χ, ?_⟩
      exact (discreteSeriesClassHaarScalingEquiv_smul A hA μ ν c χ η).symm.trans
        (congrArg (discreteSeriesClassHaarScalingEquiv A hA μ c) hχ))
  invFun := Quotient.map (discreteSeriesClassHaarScalingEquiv A hA μ c).symm
    (by
      intro ω η h
      obtain ⟨χ, hχ⟩ := h
      refine ⟨χ, ?_⟩
      exact (discreteSeriesClassHaarScalingEquiv_symm_smul A hA μ ν c χ η).symm.trans
        (congrArg (discreteSeriesClassHaarScalingEquiv A hA μ c).symm hχ))
  left_inv O := by
    induction O using Quotient.inductionOn with
    | h ω =>
      exact congrArg (Quotient.mk _)
        ((discreteSeriesClassHaarScalingEquiv A hA μ c).symm_apply_apply ω)
  right_inv O := by
    induction O using Quotient.inductionOn with
    | h ω =>
      exact congrArg (Quotient.mk _)
        ((discreteSeriesClassHaarScalingEquiv A hA μ c).apply_symm_apply ω)

@[simp]
theorem discreteSeriesOrbitHaarScalingEquiv_mk
    (c : ℝ≥0) [NeZero c] (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesOrbitHaarScalingEquiv A hA μ ν c (Quotient.mk _ ω) =
      Quotient.mk _ (discreteSeriesClassHaarScalingEquiv A hA μ c ω) :=
  rfl

variable [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

/-- The transported orbit's actual Schur degree is divided by the Haar scalar. -/
theorem discreteSeriesOrbitFormalDegree_smul_measure
    (c : ℝ≥0) [NeZero c] (O : DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μ ν) :
    discreteSeriesOrbitFormalDegree A hA (c • μ) hcof ν
        (discreteSeriesOrbitHaarScalingEquiv A hA μ ν c O) =
      (c : ℝ)⁻¹ * discreteSeriesOrbitFormalDegree A hA μ hcof ν O := by
  induction O using Quotient.inductionOn with
  | h ω =>
    rw [discreteSeriesOrbitHaarScalingEquiv_mk, discreteSeriesOrbitFormalDegree_mk,
      discreteSeriesOrbitFormalDegree_mk]
    exact discreteSeriesFormalDegree_smul_measure A hA μ hcof c ω

end Langlands.Plancherel
