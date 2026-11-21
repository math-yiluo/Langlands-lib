import Langlands.Global.RankinSelberg.ComplexLocalCompactWhittakerAveraging
import Langlands.Global.RankinSelberg.ComplexLocalCompactProjectionExistence
import Langlands.Global.RankinSelberg.ComplexLocalIntertwinerAnalytic
import Langlands.Global.RankinSelberg.ComplexMatrixConnected

/-! # Matched compact projections for complex Whittaker coefficients -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "I" => matrixModel ℂ n
local notation "E[" ds "]" => complexStandardKFinite n ds

variable (r) in
/-- Compact convolution in the inducing space realizes the same convolution
of the corresponding Whittaker coefficient. -/
def ComplexLocalCompactMatchedProjectionStatement : Prop :=
  ∀ (ds : List ComplexCharacterData) (a : ℂˣ) (ν : Measure Kc), ν.IsHaarMeasure →
  ∀ (κ : Kc → ℂ), Continuous κ →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x : Kc => fun k => κ (x⁻¹ * k))) →
  ∀ (B : E[ds] →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∀ (f : E[ds]),
    ∃ p : G → E[ds],
      (∀ (g : G) (k : Kc), (p g : G → ℂ) k.val = ∫ l, κ l * (f : G → ℂ) (k.val * l.val * g) ∂ν) ∧
      ∀ x g : G, B (p g) x = ∫ k, κ k * B f (x * k.val * g) ∂ν

theorem complexLocalCompactMatchedProjection : ComplexLocalCompactMatchedProjectionStatement r := by
  intro ds a ν hν κ hκ hκfin B hB f
  classical
  choose p hp using fun v => complexLocalCompactProjectionExists ds ν hν κ hκ hκfin v
  refine ⟨p f, hp f, fun x g => ?_⟩
  let κc : C(Kc, ℂ) := ⟨κ, hκ⟩
  have hAn (es : List ComplexCharacterData) (A : E[es] →ₗ[ℂ] (G → ℂ))
      (hSm : ∀ v, ContMDiff I 𝓘(ℝ, ℂ) ∞ (A v))
      (hD : ∀ Y v, A (complexStandardLie n es (1 ⊗ₜ[ℝ] Y) v) = rightDerivative I Y (A v))
      (v : E[es]) : AnalyticOnNhd ℝ (unitsExtension (A v)) {Y : M | IsUnit Y} := by
    apply analyticOnNhd_unitsExtension_of_standardLie_intertwining A hSm _ v
    intro Y w
    have hact :
        envelopingAction (complexStandardLie n es) (ComplexLocalCasimir.realGenerator n Y) =
          complexStandardLie n es (1 ⊗ₜ[ℝ] Y) := by
      change envelopingAction (complexStandardLie n es)
        (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y)) = _
      exact UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ _
    rw [hact]
    exact hD Y w
  exact complexLocalCompactWhittakerAveraging (complexMatrixUnitsPreconnected n) hAn
    ds a ν hν κc (hasFiniteCompactConvolutionKernel_of_finite_translates κ hκ hκfin)
    B hB p hp f g x

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
