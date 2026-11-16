import Langlands.Global.RankinSelberg.EqualUnfoldingGaugeStatement
import Langlands.Global.RankinSelberg.UnequalGaugeReduction
import Langlands.Global.RankinSelberg.SchwartzBruhatProof.Fourier

/-! # The dual equal-rank gauge premise from a Whittaker-Schwartz estimate -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance equalDualGaugeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalDualGaugeSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The weighted integral of the dual Whittaker function times any Schwartz--Bruhat
function of the last row is finite sufficiently far to the right, with a threshold
independent of the standard character, vector and Schwartz--Bruhat function. -/
def DualEqualWhittakerSchwartzBound {r : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) → ∀ σ : ℝ, C < σ →
        ∫⁻ p : WhittakerQuotient F (r + 1),
            ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v) p.out‖ₑ *
              ‖Φ (lastRow F r p.out)‖ₑ * ENNReal.ofReal (detNorm F (r + 1) p.out ^ σ)
          ∂whittakerQuotientMeasure F (r + 1) < ⊤

namespace EqualGaugeDualReduction

variable {r : ℕ}

/-- The absolute value of the dual Whittaker function is left unipotent invariant. -/
theorem norm_dualCuspWhittaker_unipotent_mul
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)) :
    ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v) ((n : Points F (r + 1)) * g)‖ =
      ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v) g‖ := by
  have h := dualCuspWhittaker_unipotent_mul F T ψ⁻¹
    (isStandardAdditiveCharacter_inv F ψ hψ) v n g
  rw [inv_inv] at h
  rw [h, norm_mul,
    norm_genericCharacter F r ψ⁻¹ (isStandardAdditiveCharacter_inv F ψ hψ).2.2.2, one_mul]

/-- The dual Whittaker--Schwartz bound implies the dual gauge premise. The second
cusp factor contributes only a fixed shift in the convergence threshold. -/
theorem dualEqualWhittakerGaugeIntegrable_of_schwartzBound
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (hW : DualEqualWhittakerSchwartzBound F T) :
    DualEqualWhittakerGaugeIntegrable F T T' := by
  obtain ⟨C₀, -, hW⟩ := hW
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_dualCuspFunction_le F T'
  refine ⟨max 0 (C₀ - β), le_max_left _ _, fun ψ hψ v v' Φ hΦ s hs => ?_⟩
  obtain ⟨C', hC'0, hC'⟩ := hβ v'
  let Ψ := fourierTransform F (r + 1) ψ Φ
  have hΨ : Ψ ∈ schwartzBruhat F (r + 1) :=
    (SchwartzBruhatProof.fourierTransform_mem_and_inversion (r + 1) ψ hψ hΦ).1
  have hΨm : Measurable (fun g : Points F (r + 1) => Ψ (lastRow F r g)) :=
    EqualUnfolding.measurable_lastRow_comp
      (EqualUnfolding.measurable_of_mem_schwartzBruhat F hΨ)
  let σ := s.re + β
  have hσ : C₀ < σ := by
    dsimp [σ]
    linarith [le_max_right 0 (C₀ - β)]
  have hfin := hW ψ hψ v Ψ hΨ σ hσ
  let W := dualFunction F (r + 1) (cuspWhittaker F T ψ v)
  let φ' := dualFunction F (r + 1) (cuspFunction F T' v')
  have hWm : Measurable W :=
    (measurable_cuspWhittaker F T ψ hψ v).comp (continuous_dualPoint F (r + 1)).measurable
  have hWθ : ∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      W ((n : Points F (r + 1)) * g) = genericCharacter F r ψ⁻¹ (fun _ => 1) n * W g := by
    intro n g
    have h := dualCuspWhittaker_unipotent_mul F T ψ⁻¹
      (isStandardAdditiveCharacter_inv F ψ hψ) v n g
    rwa [inv_inv] at h
  have hfm : Measurable (EqualUnfolding.equalKernel F W φ' Ψ s) :=
    EqualUnfolding.measurable_equalKernel F hWm
      (continuous_dualCuspFunction F T' v').measurable hΨm s
  have hfΓ : ∀ (k : unipotentRationalImage F (r + 1)) (g : Points F (r + 1)),
      EqualUnfolding.equalKernel F W φ' Ψ s ((k : Points F (r + 1)) * g) =
        EqualUnfolding.equalKernel F W φ' Ψ s g := fun k g =>
    EqualUnfolding.equalKernel_rational_unipotent_mul F ψ⁻¹
      (isStandardAdditiveCharacter_inv F ψ hψ) Ψ s
      (fun k hk x => dualCuspFunction_rational_mul F T' v' hk x) hWθ k.property g
  let M : Points F (r + 1) → ℝ≥0∞ := fun g =>
    ‖W g‖ₑ * ‖Ψ (lastRow F r g)‖ₑ * ENNReal.ofReal (detNorm F (r + 1) g ^ σ)
  have hM : Measurable M :=
    (hWm.enorm.mul hΨm.enorm).mul
      ((continuous_detNorm F (r + 1)).measurable.pow_const σ).ennreal_ofReal
  have hMN : ∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      M ((n : Points F (r + 1)) * g) = M g := by
    intro n g
    simp only [M]
    rw [← ofReal_norm, ← ofReal_norm,
      norm_dualCuspWhittaker_unipotent_mul F T ψ hψ v n g,
      EqualUnfolding.lastRow_unipotent_mul, GaugeReduction.detNorm_unipotent_mul]
    simp only [ofReal_norm, W]
  have hbound : ∀ g : Points F (r + 1),
      ‖EqualUnfolding.equalKernel F W φ' Ψ s g‖ₑ ≤ ENNReal.ofReal C' * M g := by
    intro g
    have hd := detNorm_pos F (r + 1) g
    have hreal : ‖EqualUnfolding.equalKernel F W φ' Ψ s g‖ ≤
        C' * (‖W g‖ * ‖Ψ (lastRow F r g)‖ * detNorm F (r + 1) g ^ σ) := by
      unfold EqualUnfolding.equalKernel
      rw [norm_mul, norm_mul, norm_mul, GaugeReduction.norm_detPower_eq_rpow]
      calc ‖W g‖ * ‖φ' g‖ * ‖Ψ (lastRow F r g)‖ * detNorm F (r + 1) g ^ s.re
          ≤ ‖W g‖ * (C' * detNorm F (r + 1) g ^ β) *
              ‖Ψ (lastRow F r g)‖ * detNorm F (r + 1) g ^ s.re := by
            gcongr
            exact hC' g
        _ = C' * (‖W g‖ * ‖Ψ (lastRow F r g)‖ * detNorm F (r + 1) g ^ σ) := by
            rw [show σ = s.re + β from rfl, Real.rpow_add hd]
            ring
    calc ‖EqualUnfolding.equalKernel F W φ' Ψ s g‖ₑ
        = ENNReal.ofReal ‖EqualUnfolding.equalKernel F W φ' Ψ s g‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (C' *
          (‖W g‖ * ‖Ψ (lastRow F r g)‖ * detNorm F (r + 1) g ^ σ)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C' * M g := by
          simp only [M]
          rw [ENNReal.ofReal_mul hC'0,
            ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
            ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  show Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
    EqualUnfolding.equalKernel F W φ' Ψ s q.out) _
  refine ⟨?_, ?_⟩
  · have hm : Measurable (LeftCosetSpace.lift (unipotentRationalImage F (r + 1)) _ hfΓ) :=
      measurable_from_quotient.mpr hfm
    rw [out_eq_lift _ _ hfΓ]
    exact hm.aestronglyMeasurable
  · calc ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (r + 1)),
          ‖EqualUnfolding.equalKernel F W φ' Ψ s q.out‖ₑ
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
            (isDiscrete_unipotentRationalImage F (r + 1))
        ≤ ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (r + 1)),
            ENNReal.ofReal C' * M q.out
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
            (isDiscrete_unipotentRationalImage F (r + 1)) :=
          lintegral_mono fun q => hbound q.out
      _ = ENNReal.ofReal C' * ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (r + 1)),
            M q.out
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
            (isDiscrete_unipotentRationalImage F (r + 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C' *
          ∫⁻ p : WhittakerQuotient F (r + 1), M p.out
            ∂whittakerQuotientMeasure F (r + 1) := by
          rw [GaugeReduction.lintegral_rationalQuotient_eq F hM hMN]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end EqualGaugeDualReduction

end Langlands.Global.RankinSelbergGlobal
