import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeMellinStatement
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeHaarModulus
import Langlands.Global.RankinSelberg.WhittakerStandardCompactTorusIntegral
import Langlands.Global.RankinSelberg.DetNormCompactIntegrals

/-! # Padded Mellin convergence for adelic simple-root gauges -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding WhittakerStandardCompactTorusIntegral

local instance mellinProofSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance mellinProofSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local instance : MeasurableSpace (Ideles F) := borel _
local instance : BorelSpace (Ideles F) := ⟨rfl⟩
local instance : LocallyCompactSpace (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance : SecondCountableTopology (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology

/-- The inverse-modulus torus estimate gives unconditional convergence on the
actual Whittaker quotient, at the same exponent threshold. -/
theorem IsAdelicSimpleRootGauge.lintegral_padded_whittakerQuotient_of_large
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ) {σ : ℝ}
    (hσ : τ + 3 + ∑ j : Fin (t + 1),
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) < σ) :
    ∫⁻ p : WhittakerQuotient F (t + 1),
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) p.out) *
        ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
      ∂whittakerQuotientMeasure F (t + 1) < ⊤ := by
  let hp := Nat.le_of_lt (Nat.succ_lt_succ h)
  let f : Points F (t + 1) → ℝ≥0∞ := fun g =>
    Ξ (pad F hp g) * ENNReal.ofReal (detNorm F (t + 1) g ^ σ)
  have hpow : Continuous fun g : Points F (t + 1) => detNorm F (t + 1) g ^ σ :=
    (continuous_detNorm F (t + 1)).rpow_const fun g =>
      Or.inl (detNorm_pos F (t + 1) g).ne'
  have hfm : Measurable f :=
    (hΞ.2.1.comp (continuous_pad F hp).measurable).mul
      (ENNReal.measurable_ofReal.comp hpow.measurable)
  have hfN : ∀ (v : unipotentAdelic F (t + 1)) (g : Points F (t + 1)),
      f ((v : Points F (t + 1)) * g) = f g := by
    intro v g
    dsimp only [f]
    rw [pad_mul]
    have hv := hΞ.2.2.1 (padUnipotent F hp v) (pad F hp g)
    change Ξ (pad F hp (v : Points F (t + 1)) * pad F hp g) =
      Ξ (pad F hp g) at hv
    rw [hv]
    rw [detNorm_mul, detNorm_unipotent, one_mul]
  have hfK : IsRightStandardCompactInvariant F (t + 1) f := by
    intro k g
    dsimp only [f]
    rw [pad_mul]
    rw [hΞ.2.2.2.1
      ⟨pad F hp (k : Points F (t + 1)),
        pad_mem_standardCompact F hp k k.property⟩]
    rw [detNorm_mul, detNorm_eq_one_of_mem_standardCompact F k.property, mul_one]
  apply lintegral_whittakerQuotient_lt_top_of_single F (t + 1)
    (Measure.haar : Measure (Fin (t + 1) → Ideles F)) f hfm hfN hfK
  simpa only [f, gaugeDiagonalInverseHaarWeight, mul_comm] using
    hΞ.lintegral_padded_torus_mul_inverseHaarModulus_of_large F h
      (Measure.haar : Measure (Fin (t + 1) → Ideles F)) hσ

/-- A common half-plane works for all gauges of a fixed exponent. -/
theorem adelicSimpleRootGaugeMellin :
    AdelicSimpleRootGaugeMellinStatement.{u} := by
  intro F _ _ _ r t h τ _hτ
  let T := τ + 3 + ∑ j : Fin (t + 1),
    ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ)
  refine ⟨max 0 T, le_max_left _ _, fun Ξ hΞ σ hσ => ?_⟩
  exact hΞ.lintegral_padded_whittakerQuotient_of_large F h
    ((le_max_right 0 T).trans_lt hσ)

end Langlands.Global.RankinSelbergGlobal
