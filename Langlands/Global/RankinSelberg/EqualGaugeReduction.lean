import Langlands.Global.RankinSelberg.EqualUnfoldingGaugeStatement
import Langlands.Global.RankinSelberg.UnequalGaugeReduction

/-! # Removing the second cusp form from the equal-rank gauge premise

The remaining analytic input is a weighted Whittaker–Schwartz integral on
`N_n(𝔸) \ GL_n(𝔸)`. A fixed central-power bound for the second cusp form
then gives integrability of the unfolding kernel on `N_n(F) \ GL_n(𝔸)`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance equalGaugeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalGaugeSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The weighted Whittaker–Schwartz integral is finite for all real exponents above
one nonnegative bound depending only on the cuspidal realization. -/
def EqualWhittakerSchwartzBound {r : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) → ∀ σ : ℝ, C < σ →
        ∫⁻ p : WhittakerQuotient F (r + 1),
            ‖cuspWhittaker F T ψ v p.out‖ₑ * ‖Φ (lastRow F r p.out)‖ₑ *
              ENNReal.ofReal (detNorm F (r + 1) p.out ^ σ)
          ∂whittakerQuotientMeasure F (r + 1) < ⊤

/-- The Whittaker–Schwartz bound for every actual cuspidal realization. -/
def EqualWhittakerSchwartzStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r),
    EqualWhittakerSchwartzBound F T

/-- The Whittaker–Schwartz statement implies the primal equal-rank gauge premise
for every pair of cuspidal realizations. -/
def EqualGaugeReductionStatement : Prop :=
  EqualWhittakerSchwartzStatement.{u} →
    ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r : ℕ) (T T' : Automorphic.CuspidalOperatorRealization F r),
      EqualWhittakerGaugeIntegrable F T T'

namespace EqualGaugeReduction

variable {r : ℕ}

omit [CompactSpace (AdeleQuotient F)] in
/-- A finite weighted Whittaker–Schwartz integral and a central-power bound for a
rational-invariant second function imply integrability of their equal-rank kernel. -/
theorem integrable_equalKernel_of_bound
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    {W φ' : Points F (r + 1) → ℂ} {Φ : RowVector F (r + 1) → ℂ} (s : ℂ)
    (hWm : Measurable W) (hφ'm : Measurable φ')
    (hΦm : Measurable fun g => Φ (lastRow F r g))
    (hWθ : ∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      W ((n : Points F (r + 1)) * g) = genericCharacter F r ψ (fun _ => 1) n * W g)
    (hφ'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)),
      ∀ g, φ' (k * g) = φ' g)
    (B β : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ g, ‖φ' g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (hfin : ∫⁻ p : WhittakerQuotient F (r + 1),
        ‖W p.out‖ₑ * ‖Φ (lastRow F r p.out)‖ₑ *
          ENNReal.ofReal (detNorm F (r + 1) p.out ^ (s.re + β))
      ∂whittakerQuotientMeasure F (r + 1) < ⊤) :
    Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
        EqualUnfolding.equalKernel F W φ' Φ s q.out)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
        (isDiscrete_unipotentRationalImage F (r + 1))) := by
  let M : Points F (r + 1) → ℝ≥0∞ := fun g =>
    ‖W g‖ₑ * ‖Φ (lastRow F r g)‖ₑ *
      ENNReal.ofReal (detNorm F (r + 1) g ^ (s.re + β))
  have hM : Measurable M :=
    (hWm.enorm.mul hΦm.enorm).mul
      ((continuous_detNorm F (r + 1)).measurable.pow_const (s.re + β)).ennreal_ofReal
  have hMN : ∀ (n : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      M ((n : Points F (r + 1)) * g) = M g := by
    intro n g
    simp only [M, ← ofReal_norm]
    rw [hWθ, norm_mul, norm_genericCharacter F r ψ hψ.2.2.2, one_mul,
      EqualUnfolding.lastRow_unipotent_mul, GaugeReduction.detNorm_unipotent_mul]
  have hmajorant : ∀ g : Points F (r + 1),
      ‖EqualUnfolding.equalKernel F W φ' Φ s g‖ₑ ≤ ENNReal.ofReal B * M g := by
    intro g
    have hd := detNorm_pos F (r + 1) g
    have hreal : ‖EqualUnfolding.equalKernel F W φ' Φ s g‖ ≤
        B * (‖W g‖ * ‖Φ (lastRow F r g)‖ * detNorm F (r + 1) g ^ (s.re + β)) := by
      unfold EqualUnfolding.equalKernel
      rw [norm_mul, norm_mul, norm_mul, GaugeReduction.norm_detPower_eq_rpow]
      calc ‖W g‖ * ‖φ' g‖ * ‖Φ (lastRow F r g)‖ * detNorm F (r + 1) g ^ s.re
          ≤ ‖W g‖ * (B * detNorm F (r + 1) g ^ β) *
              ‖Φ (lastRow F r g)‖ * detNorm F (r + 1) g ^ s.re := by
            gcongr
            exact hbound g
        _ = B * (‖W g‖ * ‖Φ (lastRow F r g)‖ * detNorm F (r + 1) g ^ (s.re + β)) := by
            rw [Real.rpow_add hd]
            ring
    calc ‖EqualUnfolding.equalKernel F W φ' Φ s g‖ₑ =
        ENNReal.ofReal ‖EqualUnfolding.equalKernel F W φ' Φ s g‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal
          (B * (‖W g‖ * ‖Φ (lastRow F r g)‖ * detNorm F (r + 1) g ^ (s.re + β))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal B * M g := by
        simp only [M]
        rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _)
          (norm_nonneg _)), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  have hfΓ : ∀ (k : unipotentRationalImage F (r + 1)) (g : Points F (r + 1)),
      EqualUnfolding.equalKernel F W φ' Φ s ((k : Points F (r + 1)) * g) =
        EqualUnfolding.equalKernel F W φ' Φ s g :=
    fun k g => EqualUnfolding.equalKernel_rational_unipotent_mul F ψ hψ Φ s
      hφ'Γ hWθ k.property g
  refine ⟨?_, ?_⟩
  · have hm : Measurable (LeftCosetSpace.lift (unipotentRationalImage F (r + 1))
        (EqualUnfolding.equalKernel F W φ' Φ s) hfΓ) :=
      measurable_from_quotient.mpr
        (EqualUnfolding.measurable_equalKernel F hWm hφ'm hΦm s)
    rw [out_eq_lift _ _ hfΓ]
    exact hm.aestronglyMeasurable
  · calc ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (r + 1)),
          ‖EqualUnfolding.equalKernel F W φ' Φ s q.out‖ₑ
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
            (isDiscrete_unipotentRationalImage F (r + 1))
        ≤ ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (r + 1)),
            ENNReal.ofReal B * M q.out
          ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
            (isDiscrete_unipotentRationalImage F (r + 1)) :=
          lintegral_mono fun q => hmajorant q.out
      _ = ENNReal.ofReal B *
          ∫⁻ q : LeftCosetSpace (unipotentRationalImage F (r + 1)), M q.out
            ∂LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
              (isDiscrete_unipotentRationalImage F (r + 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal B *
          ∫⁻ p : WhittakerQuotient F (r + 1), M p.out
            ∂whittakerQuotientMeasure F (r + 1) := by
          rw [GaugeReduction.lintegral_rationalQuotient_eq F hM hMN]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The Whittaker–Schwartz bound implies the primal equal-rank gauge premise. -/
theorem equalWhittakerGaugeIntegrable_of_schwartzBound
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (hW : EqualWhittakerSchwartzBound F T) : EqualWhittakerGaugeIntegrable F T T' := by
  obtain ⟨C, -, hW⟩ := hW
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_cuspFunction_le F T'
  refine ⟨max 0 (C - β), le_max_left _ _, fun ψ hψ v v' Φ hΦ s hs => ?_⟩
  obtain ⟨B, hB, hb⟩ := hβ v'
  have hσ : C < s.re + β := by linarith [le_max_right 0 (C - β)]
  exact integrable_equalKernel_of_bound F ψ hψ s
    (measurable_cuspWhittaker F T ψ hψ v) (continuous_cuspFunction F T' v').measurable
    (EqualUnfolding.measurable_lastRow_comp
      (EqualUnfolding.measurable_of_mem_schwartzBruhat F hΦ))
    (cuspWhittaker_mul_left F T ψ hψ v)
    (fun k hk g => cuspFunction_rational_mul F T' v' hk g) B β hB hb
    (hW ψ hψ v Φ hΦ (s.re + β) hσ)

end EqualGaugeReduction

/-- Proof of the conditional primal gauge reduction. -/
theorem equalGaugeReduction : EqualGaugeReductionStatement.{u} := by
  intro h F _ _ _ r T T'
  exact EqualGaugeReduction.equalWhittakerGaugeIntegrable_of_schwartzBound F T T'
    (h F r T)

end Langlands.Global.RankinSelbergGlobal
