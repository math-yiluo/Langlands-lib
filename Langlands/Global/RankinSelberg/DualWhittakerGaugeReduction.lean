import Langlands.Global.RankinSelberg.WhittakerSimpleRootMajorizationStatement
import Langlands.Global.RankinSelberg.DualWhittakerExpansionProof
import Langlands.Global.RankinSelberg.EqualGaugeDualSpecialization
import Langlands.Global.RankinSelberg.UnfoldingWeylCompact

/-! # Translated dual Whittaker majorization from the generic gauge input -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding Langlands.Automorphic

local instance dualGaugeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The unfolding Weyl representative has determinant norm one. -/
theorem detNorm_unfoldingWeyl {r t : ℕ} (h : t < r) :
    detNorm F (r + 1) (unfoldingWeyl F h) = 1 := by
  have hinv : (unfoldingWeyl F h)⁻¹ = unfoldingWeyl F h := by
    rw [unfoldingWeyl, ← map_inv, ← map_inv, ← map_inv, Prod.inv_mk, inv_one,
      GeneralLinear.weylLong_inv]
  have hsquare : unfoldingWeyl F h * unfoldingWeyl F h = 1 := by
    calc
      unfoldingWeyl F h * unfoldingWeyl F h =
          (unfoldingWeyl F h)⁻¹ * unfoldingWeyl F h := by rw [hinv]
      _ = 1 := inv_mul_cancel _
  have hnorm : detNorm F (r + 1) (unfoldingWeyl F h) *
      detNorm F (r + 1) (unfoldingWeyl F h) = 1 := by
    rw [← detNorm_mul, hsquare]
    simp only [detNorm, map_one, Units.val_one, NNReal.coe_one]
  have hpos := detNorm_pos F (r + 1) (unfoldingWeyl F h)
  nlinarith

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

/-- The realization space identified with its dual cusp-function space. -/
def dualCuspSpaceEquiv : T.Space ≃ₗ[ℂ] iotaSpace F (cuspSpace F T) :=
  (cuspEquiv F T).trans (iotaSpaceEquiv F (cuspSpace F T))

/-- The function represented by the dual cusp-space equivalence is the dual
of the original cusp function. -/
theorem coe_dualCuspSpaceEquiv (v : T.Space) :
    ((dualCuspSpaceEquiv F T v : iotaSpace F (cuspSpace F T)) :
      Points F (r + 1) → ℂ) = dualFunction F (r + 1) (cuspFunction F T v) :=
  coe_iotaSpaceEquiv_cuspEquiv F T v

/-- The generic majorization statement gives a common pair of exponents for
the dual Whittaker functions of an actual cuspidal realization. -/
theorem dualCuspWhittaker_majorization_of_simpleRoot
    (hmajorization : WhittakerSimpleRootMajorizationStatement.{u}) :
    ∃ β τ : ℝ, 0 ≤ τ ∧ ∀ (ψ : AddChar (Adeles F) ℂ),
      IsStandardAdditiveCharacter F ψ → ∀ v : T.Space,
        ∃ Ξ : Points F (r + 1) → ℝ≥0∞, IsAdelicSimpleRootGauge F r τ Ξ ∧
          ∀ g : Points F (r + 1),
            ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v) g‖ₑ ≤
              ENNReal.ofReal (detNorm F (r + 1) g ^ β) * Ξ g := by
  obtain ⟨β, hβ⟩ := EqualGaugeDualSpecialization.exists_norm_iotaCuspSpace_le F T
  obtain ⟨τ, hτ, hmajor⟩ :=
    hmajorization F r (iotaSpace F (cuspSpace F T))
      (iotaDerivative F (cuspSpace F T) (cuspDerivative F T))
      (whittakerDecayClass_iotaSpace (whittakerDecayClass_cuspSpace F T)) β hβ
  refine ⟨β, τ, hτ, fun ψ hψ v => ?_⟩
  obtain ⟨Ξ, hΞ, hW⟩ := hmajor ψ⁻¹ (isStandardAdditiveCharacter_inv F ψ hψ)
    (dualCuspSpaceEquiv F T v)
  refine ⟨Ξ, hΞ, fun g => ?_⟩
  rw [dualCuspWhittaker_eq_whittaker F T ψ hψ]
  simpa only [coe_dualCuspSpaceEquiv] using hW g

/-- Compact right translation by the unfolding Weyl representative preserves
the dual majorant and both exponents. -/
theorem translatedDualCuspWhittaker_majorization_of_simpleRoot {t : ℕ} (h : t < r)
    (hmajorization : WhittakerSimpleRootMajorizationStatement.{u}) :
    ∃ β τ : ℝ, 0 ≤ τ ∧ ∀ (ψ : AddChar (Adeles F) ℂ),
      IsStandardAdditiveCharacter F ψ → ∀ v : T.Space,
        ∃ Ξ : Points F (r + 1) → ℝ≥0∞, IsAdelicSimpleRootGauge F r τ Ξ ∧
          ∀ g : Points F (r + 1),
            ‖translateFunction F (r + 1) (unfoldingWeyl F h)
                (dualFunction F (r + 1) (cuspWhittaker F T ψ v)) g‖ₑ ≤
              ENNReal.ofReal (detNorm F (r + 1) g ^ β) * Ξ g := by
  obtain ⟨β, τ, hτ, hmajor⟩ :=
    dualCuspWhittaker_majorization_of_simpleRoot F T hmajorization
  refine ⟨β, τ, hτ, fun ψ hψ v => ?_⟩
  obtain ⟨Ξ, hΞ, hW⟩ := hmajor ψ hψ v
  refine ⟨Ξ, hΞ, fun g => ?_⟩
  have hw : unfoldingWeyl F h ∈ gaugeStandardCompact F (r + 1) :=
    unfoldingWeyl_mem_standardCompact F h
  have hinv := hΞ.2.2.2.1 ⟨unfoldingWeyl F h, hw⟩ g
  have hb := hW (g * unfoldingWeyl F h)
  rw [detNorm_mul, detNorm_unfoldingWeyl, mul_one, hinv] at hb
  exact hb

end Langlands.Global.RankinSelbergGlobal
