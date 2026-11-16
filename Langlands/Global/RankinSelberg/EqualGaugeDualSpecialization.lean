import Langlands.Global.RankinSelberg.EqualGaugeDualReduction
import Langlands.Global.RankinSelberg.DualWhittakerExpansionProof
import Langlands.Global.RankinSelberg.WhittakerSchwartzGaugeStatement

/-! # Applying a general Whittaker--Schwartz estimate to the dual cusp space -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance dualGaugeSpecializationAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualGaugeSpecializationSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- The general weighted estimate implies the dual equal-rank gauge premise
for every pair of actual cuspidal realizations. -/
def EqualGaugeDualSpecializationStatement : Prop :=
  WhittakerSchwartzGaugeStatement.{u} →
    ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r : ℕ) (T T' : Automorphic.CuspidalOperatorRealization F r),
      DualEqualWhittakerGaugeIntegrable F T T'

namespace EqualGaugeDualSpecialization

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)

/-- One determinant exponent bounds all functions of the transpose-inverse cusp space. -/
theorem exists_norm_iotaCuspSpace_le :
    ∃ β : ℝ, ∀ f : iotaSpace F (cuspSpace F T), ∃ B : ℝ, 0 ≤ B ∧
      ∀ g : Points F (r + 1),
        ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β := by
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_dualCuspFunction_le F T
  refine ⟨β, fun f => ?_⟩
  let v : T.Space := (cuspEquiv F T).symm ((iotaSpaceEquiv F (cuspSpace F T)).symm f)
  have hv : cuspEquiv F T v = (iotaSpaceEquiv F (cuspSpace F T)).symm f :=
    (cuspEquiv F T).apply_symm_apply _
  have hf := coe_iotaSpaceEquiv_cuspEquiv F T v
  rw [hv, LinearEquiv.apply_symm_apply] at hf
  obtain ⟨B, hB0, hB⟩ := hβ v
  refine ⟨B, hB0, fun g => ?_⟩
  rw [hf]
  exact hB g

/-- A uniform Whittaker--Schwartz bound on the transpose-inverse cusp space gives
its dual-Whittaker form for the original realization. -/
theorem dualEqualWhittakerSchwartzBound_of_iotaSpace
    (hW : WhittakerSchwartzBound F r (iotaSpace F (cuspSpace F T))) :
    DualEqualWhittakerSchwartzBound F T := by
  obtain ⟨C, hC0, hW⟩ := hW
  refine ⟨C, hC0, fun ψ hψ v Φ hΦ σ hσ => ?_⟩
  have h := hW ψ⁻¹ (isStandardAdditiveCharacter_inv F ψ hψ)
    (iotaSpaceEquiv F (cuspSpace F T) (cuspEquiv F T v)) Φ hΦ σ hσ
  simpa only [coe_iotaSpaceEquiv_cuspEquiv,
    ← dualCuspWhittaker_eq_whittaker F T ψ hψ v] using h

/-- Specialize the general weighted estimate to the transpose-inverse cusp space. -/
theorem dualEqualWhittakerSchwartzBound
    (h : WhittakerSchwartzGaugeStatement.{u}) :
    DualEqualWhittakerSchwartzBound F T := by
  apply dualEqualWhittakerSchwartzBound_of_iotaSpace F T
  exact h F r (iotaSpace F (cuspSpace F T))
    (iotaDerivative F (cuspSpace F T) (cuspDerivative F T))
    (whittakerDecayClass_iotaSpace (whittakerDecayClass_cuspSpace F T))
    (exists_norm_iotaCuspSpace_le F T)

/-- The specialized estimate gives the dual gauge premise for any second realization. -/
theorem dualEqualWhittakerGaugeIntegrable
    (T' : Automorphic.CuspidalOperatorRealization F r)
    (h : WhittakerSchwartzGaugeStatement.{u}) :
    DualEqualWhittakerGaugeIntegrable F T T' :=
  EqualGaugeDualReduction.dualEqualWhittakerGaugeIntegrable_of_schwartzBound F T T'
    (dualEqualWhittakerSchwartzBound F T h)

end EqualGaugeDualSpecialization

/-- The general estimate supplies all dual equal-rank gauge premises. -/
theorem equalGaugeDualSpecialization : EqualGaugeDualSpecializationStatement.{u} := by
  intro h F _ _ _ r T T'
  exact EqualGaugeDualSpecialization.dualEqualWhittakerGaugeIntegrable F T T' h

end Langlands.Global.RankinSelbergGlobal
