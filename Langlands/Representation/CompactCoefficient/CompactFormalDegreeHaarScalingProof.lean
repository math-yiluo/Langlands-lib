import Langlands.Representation.CompactCoefficient.CompactFormalDegreeHaarScalingStatement

/-! # Proof of Renard IV.1.4, Remark 1: the formal degree and the Haar measure

The integrated Hecke action for `c • μ` is `c` times the action for `μ`. The formal-degree
identity for `μ` and `κ` is therefore equivalent to the identity for `c • μ` and `c κ`.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Renard.CompactRepresentation

open HarmonicAnalysis

/-- The integrated action against `c • μ` is `c` times the integrated action against `μ`.
Both sides are compared through every algebraic linear functional, where the action is an
ordinary Bochner integral that scales with the measure. -/
theorem integratedAction_nnreal_smul_measure {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (c : ℝ≥0)
    [IsFiniteMeasureOnCompacts (c • μ)]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (f : SchwartzBruhat G) (x : V) :
    Hecke.integratedAction (c • μ) ρ hρ f x =
      ((c : ℝ) : ℂ) • Hecke.integratedAction μ ρ hρ f x := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero, map_smul, Hecke.integratedAction_dual,
    Hecke.integratedAction_dual, integral_smul_nnreal_measure]
  change (c : ℝ) • (_ : ℂ) = _
  rw [Complex.real_smul, smul_eq_mul]

/-- The Hecke action against `c • μ` is `c` times the Hecke action against `μ`, for the same
underlying locally constant compactly supported function. -/
theorem heckeAction_nnreal_smul_measure {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (c : ℝ≥0)
    [IsFiniteMeasureOnCompacts (c • μ)] [(c • μ).IsMulLeftInvariant]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (f : Hecke.HeckeAlgebra (c • μ)) (x : V) :
    Hecke.heckeAction (c • μ) ρ hρ f x =
      ((c : ℝ) : ℂ) • Hecke.heckeAction μ ρ hρ (show Hecke.HeckeAlgebra μ from f) x := by
  rw [Hecke.heckeAction_apply, Hecke.heckeAction_apply]
  exact integratedAction_nnreal_smul_measure μ c ρ hρ _ x

/-- Renard IV.1.4, Remark 1: `κ` satisfies the formal-degree identity for `μ` exactly when
`c κ` satisfies it for `c • μ`. -/
theorem compactFormalDegreeHaarScaling :
    CompactFormalDegreeHaarScalingStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ τ c _ κ
  have hc : ((c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne c)
  constructor
  · intro h w ℓ f hf x
    rw [heckeAction_nnreal_smul_measure μ c, h w ℓ f hf x, smul_smul, mul_assoc]
  · intro h w ℓ f hf x
    have h' := h w ℓ (show Hecke.HeckeAlgebra (c • μ) from f) hf x
    rw [heckeAction_nnreal_smul_measure μ c, mul_assoc, ← smul_smul] at h'
    exact smul_right_injective _ hc h'

end Langlands.Renard.CompactRepresentation
