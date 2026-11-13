import Langlands.Automorphic.CuspidalContragredientExistenceStatement
import Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.HeckeTwist.ContragredientTwist
import Langlands.Automorphic.HeckeTwist.FiniteSlice
import Langlands.Automorphic.HeckeTwist.FiniteLocalTransport

/-! # Existence of actual cuspidal contragredients without a unitary center

Every actual cuspidal operator realization `T` of `GL_(r+1)` has an actual cuspidal
contragredient. The realization `T` has a central character `ω`
(`OperatorRealization.existsUnique_hasCentralCharacter`). Twisting by `μ ∘ det` with
`μ = ‖ω‖ ^ (-1/(r+1))` gives a cuspidal realization with the unitary central character
`μ ^ (r+1) * ω`. The unitary case supplies a contragredient `T₀'` of this twist, and the
twist of `T₀'` by `μ ∘ det` is a contragredient of `T`
(`OperatorRealization.IsContragredientOf.of_heckeDeterminantTwist`).
-/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global
open scoped NumberField

/-- The continuous character `w ↦ ‖w‖ ^ s` of `ℂˣ`, for a real exponent `s`. -/
def unitsNormRpow (s : ℝ) : ℂˣ →ₜ* ℂˣ where
  toFun w := Units.mk0 ((‖(w : ℂ)‖ ^ s : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr w.ne_zero) s).ne')
  map_one' := Units.ext (by simp)
  map_mul' w z := Units.ext (by
    simp only [Units.val_mul, Units.val_mk0, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul])
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr <|
    Complex.continuous_ofReal.comp <|
      (continuous_norm.comp Units.continuous_val).rpow_const fun w =>
        Or.inl (norm_ne_zero_iff.mpr w.ne_zero)

theorem norm_unitsNormRpow (s : ℝ) (w : ℂˣ) :
    ‖((unitsNormRpow s w : ℂˣ) : ℂ)‖ = ‖(w : ℂ)‖ ^ s := by
  change ‖((‖(w : ℂ)‖ ^ s : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

variable {F : Type uF} [Field F] [NumberField F]

/-- The Hecke character `‖ω‖ ^ (-1/(r+1))`, whose determinant twist makes the central
character `ω` of a realization of `GL_(r+1)` unitary. -/
def unitarizingCharacter (r : ℕ) (ω : HeckeCharacter F) : HeckeCharacter F :=
  (unitsNormRpow (-1 / ((r : ℝ) + 1))).comp ω

theorem norm_unitarizingCharacter_pow_mul (r : ℕ) (ω : HeckeCharacter F) (z : IdeleClasses F) :
    ‖(((unitarizingCharacter r ω ^ (r + 1) * ω) z : ℂˣ) : ℂ)‖ = 1 := by
  rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, norm_mul, norm_pow]
  have ha : 0 < ‖((ω z : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (ω z).ne_zero
  have h₁ : ‖((unitarizingCharacter r ω z : ℂˣ) : ℂ)‖ =
      ‖((ω z : ℂˣ) : ℂ)‖ ^ (-1 / ((r : ℝ) + 1)) :=
    norm_unitsNormRpow _ (ω z)
  have h₂ : -1 / ((r : ℝ) + 1) * ((r + 1 : ℕ) : ℝ) = -1 := by
    have hr : (r : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  rw [h₁, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, h₂, Real.rpow_neg_one,
    inv_mul_cancel₀ ha.ne']

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The twist of a cuspidal realization with central character `ω` by the unitarizing
character of `ω` has a unitary central character. -/
theorem hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter
    (T : CuspidalOperatorRealization F r) {ω : HeckeCharacter F}
    (hω : T.HasCentralCharacter ω) :
    Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter
      (T.heckeDeterminantTwist (unitarizingCharacter r ω)) := by
  refine ⟨unitarizingCharacter r ω ^ (r + 1) * ω,
    norm_unitarizingCharacter_pow_mul r ω, ?_⟩
  change (T.realization.heckeDeterminantTwist
    (unitarizingCharacter r ω)).toFiniteRealization.HasCentralCharacter _
  rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
  exact FiniteRealization.heckeDeterminantTwist_hasCentralCharacter _
    (unitarizingCharacter r ω) ω hω

/-- **Existence of actual cuspidal contragredients.** Every actual cuspidal operator
realization has an actual cuspidal operator realization of the same rank realizing its
full-operator contragredient; no central-character hypothesis is needed. -/
theorem cuspidalContragredientExistence :
    CuspidalContragredientExistenceStatement.{uF} := by
  intro F _ _ _ r T
  obtain ⟨ω, hω, -⟩ :=
    OperatorRealization.existsUnique_hasCentralCharacter T.realization T.irreducible
  obtain ⟨T₀', hT₀', -⟩ := cuspidalUnitaryContragredientExistence.{uF} F r
    (T.heckeDeterminantTwist (unitarizingCharacter r ω))
    (hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter T hω)
  exact ⟨T₀'.heckeDeterminantTwist (unitarizingCharacter r ω),
    OperatorRealization.IsContragredientOf.of_heckeDeterminantTwist _ hT₀'⟩

end Langlands.Automorphic
