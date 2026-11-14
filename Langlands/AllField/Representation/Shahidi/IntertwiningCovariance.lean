import Langlands.Representation.Shahidi.IntertwiningCovariance
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.Representation.Shahidi.TwoBlocks
/-!
# Parabolic covariance of Shahidi's intertwining integral

If `f` transforms on the left under the standard `(m,n)` block parabolic by a
Levi scalar and a representation, the intertwining integral (0.1) of `f`
transforms under the `(n,m)` block parabolic, carried to total rank `m+n` by
`swapRank`, by the exchanged Levi data times the scaling factor of the change
of variables `a ↦ h₂⁻¹ a h₁`. Right invariance of `f` passes to the integral.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AllField.Shahidi
open Langlands.Shahidi hiding map_rectangularConj_padic
open Langlands.AllField.Shahidi

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis.SmoothWeakIntegral

universe uF uH uV

section Blocks


end Blocks

section Measurable

variable {F : Type uF} [Field F] [MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]

variable {m n : ℕ}

section Padic

variable (F : Type uF) [Field F] (T : LocalFieldData F)
variable [MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]

/-- Over a `p`-adic field, `a ↦ h₂⁻¹ a h₁` scales every Borel additive Haar measure
on `n × m` matrices by `|det h₂|^m |det h₁|^(-n)`. -/
theorem map_rectangularConj_padic :
    letI := T.topology
    ∀ [BorelSpace (Matrix (Fin n) (Fin m) F)]
      (μ : Measure (Matrix (Fin n) (Fin m) F)) [μ.IsAddHaarMeasure]
      (h₂ : Langlands.GeneralLinear n F) (h₁ : Langlands.GeneralLinear m F),
      μ.map (rectangularConj h₂ h₁) =
        ((T.determinantNorm n h₂ : ℝ≥0) ^ m / (T.determinantNorm m h₁ : ℝ≥0) ^ n) • μ := by
  let := T.topology
  intro _ μ _ h₂ h₁
  have h := padicRectangularHaarScaling F T n m μ h₂⁻¹ h₁⁻¹
  rw [inv_inv] at h
  change μ.map (fun a => ((h₂⁻¹ : Langlands.GeneralLinear n F) :
    Matrix (Fin n) (Fin n) F) * a * (h₁ : Matrix (Fin m) (Fin m) F)) = _
  rw [h]
  congr 1
  simp only [map_inv, Units.val_inv_eq_inv_val, inv_pow, div_eq_mul_inv, inv_inv, mul_inv]

end Padic

end Measurable

section Covariance

variable {F : Type uF} [Field F] [MeasurableSpace F]
variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable {ρ : Representation ℂ H V} {μ : Measure (Matrix (Fin n) (Fin m) F)}

section Operator


end Operator

end Covariance

end Langlands.AllField.Shahidi
