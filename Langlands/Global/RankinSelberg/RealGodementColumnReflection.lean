import Langlands.Global.RankinSelberg.RealGodementColumnQuotient
import Langlands.Global.RankinSelberg.RealGodementQuotientReflection

/-! # Reflection of the convergent real Godement column integral -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory MeasureTheory.Measure
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (d : ℕ) : MeasurableSpace (Langlands.GeneralLinear (d + 1) ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (Langlands.GeneralLinear (d + 1) ℝ) := ⟨rfl⟩
private local instance (d : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (d + 1) ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (d + 1) ℝ) := ⟨rfl⟩
private local instance (d : ℕ) : MeasurableSpace (LeftUnipotentQuotient d ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (LeftUnipotentQuotient d ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

/-- The upper-entry-product Haar is the same for opposite additive characters. -/
theorem upperStepHaar_neg (t : ℕ) (a : ℝˣ) : upperStepHaar t (-a) = upperStepHaar t a := by
  unfold upperStepHaar
  rw [RealJacquet.selfDualMeasure_neg]

/-- The Godement Whittaker integral in first-column Mellin coordinates. -/
def godementColumnValue (D : RealQuotientMeasureData t) (a : ℝˣ) (Φ : 𝓢(X, ℂ))
    (W : G → ℂ) (c : RealCharacterData) (g : H) : ℂ :=
  determinantWeight c (((t : ℂ) + 1) / 2) g *
    ∫ h, columnMellinIntegrand a (rectangularTranslate 1 g Φ) W c.parity.val
      (c.exponent + (t : ℂ) / 2) h ∂D.groupHaar

private theorem stepHaarScale_unique (a : ℝˣ) {s s' : ℝ≥0}
    (h : s • upperStepHaar t a = s' • upperStepHaar t (-a)) : s = s' := by
  let e := upperEntryCoordinates (t + 1) (K := ℝ)
  let : LocallyCompactSpace N := e.isClosedEmbedding.locallyCompactSpace
  let μ := upperStepHaar t a
  let : μ.IsHaarMeasure := upperStepHaar_isHaar t a
  have scalar (ν : Measure N) [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
      (x : ℝ≥0) (hx : ν = x • μ) : haarScalarFactor ν μ = x := by
    subst ν
    rw [haarScalarFactor_smul, haarScalarFactor_self, smul_eq_mul, mul_one]
  rw [upperStepHaar_neg] at h
  exact (scalar (s • μ) s rfl).symm.trans (scalar (s • μ) s' h)

/-- Reflection of the absolutely convergent first-column formula, with
both lower coefficients in the uniform Whittaker models at their respective signs. -/
def RealGodementColumnReflectionStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ)
    (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)) (c : RealCharacterData)
    (ds ds' : List RealBlock) (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (g : Langlands.GeneralLinear (t + 2) ℝ),
    let W' := ArchimedeanLocal.dualFunction (t + 1) W
    let g' := weylInverseTranspose (t + 2) ℝ g
    let Φ' := realRectangularSchwartzFourier a Φ
    W ∈ realUniformWhittakerModel t ds (-a) →
    W' ∈ realUniformWhittakerModel t ds' a →
    Integrable (stepGroupIntegrand a Φ W c g') D.groupHaar ∧
      Integrable (stepGroupIntegrand (-a) Φ' W' c.inverse g) D.groupHaar ∧
      godementColumnValue D a Φ W c g' =
        (c.character ((-1 : ℝˣ) ^ (t + 1)) : ℂ) *
          godementColumnValue D (-a) Φ' W' c.inverse g

theorem realGodementColumnReflection : RealGodementColumnReflectionStatement := by
  intro t D a Φ c ds ds' W g W' g' Φ' hW hW'
  have hDual : W' ∈ realUniformWhittakerModel t ds' (-(-a)) := by
    simpa only [neg_neg] using hW'
  obtain ⟨s, _, hμ, h₁⟩ := realGodementColumnQuotient t a D
  obtain ⟨s', _, hμ', h₂⟩ := realGodementColumnQuotient t (-a) D
  have hs : s = s' := stepHaarScale_unique a (hμ.symm.trans hμ')
  obtain ⟨hi₁, _, eq₁⟩ := h₁ Φ ds W c g' hW
  obtain ⟨hi₂, _, eq₂⟩ := h₂ Φ' ds' W' c.inverse g hDual
  have hR := (realGodementQuotientReflection t a c D Φ W (kernelWhittakerLaw_of_mem_model hW) g).2
  let I := ∫ q, quotientKernel a Φ W (kernelWhittakerLaw_of_mem_model hW) c g' q ∂D.measure
  let I' := ∫ q, quotientKernel (-a) Φ' W' (kernelWhittakerLaw_of_mem_model hDual) c.inverse g q ∂D.measure
  let z : ℂ := c.character ((-1 : ℝˣ) ^ (t + 1))
  have hEq : I = z * I' := hR
  refine ⟨hi₁, hi₂, ?_⟩
  calc
    godementColumnValue D a Φ W c g' = (s : ℂ) * I := eq₁
    _ = z * ((s' : ℂ) * I') := by rw [hEq, hs, mul_left_comm]
    _ = z * godementColumnValue D (-a) Φ' W' c.inverse g := congrArg (z * ·) eq₂.symm

end Langlands.Global.RankinSelbergGlobal.RealGodement
