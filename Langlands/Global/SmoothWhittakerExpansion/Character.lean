import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Continuous additive characters of `𝔸 / F` are unitary

A continuous additive character `ψ` of the adeles that is trivial on the principal adeles
factors through the compact quotient `𝔸 / F`, so its range is bounded. Since
`ψ (n • x) = ψ x ^ n` and `ψ (-x) * ψ x = 1`, every value has absolute value one. Hence a
nontrivial such character satisfies `IsStandardAdditiveCharacter`. See `Character.md`. -/

noncomputable section

universe u

open NumberField

set_option autoImplicit false

namespace Langlands.Global.SmoothWhittakerExpansion

open Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

/-- A continuous additive character of the adeles that is trivial on `F` has bounded range,
because it factors through the compact quotient `𝔸 / F`. -/
theorem exists_norm_le_of_trivial (ψ : AddChar (Adeles F) ℂ) (hc : Continuous ψ)
    (hF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    ∃ B : ℝ, ∀ x, ‖ψ x‖ ≤ B := by
  have : CompactSpace (AdeleQuotient F) := compactSpace_adeleQuotient F
  have hrel : ∀ a b : Adeles F,
      (QuotientAddGroup.leftRel (principalAdeles F)) a b → ψ a = ψ b := by
    intro a b h
    rw [QuotientAddGroup.leftRel_apply] at h
    obtain ⟨y, hy⟩ := h
    have hb : b = a + (-a + b) := by abel
    rw [hb, AddChar.map_add_eq_mul]
    change ψ a = ψ a * ψ (-a + b)
    rw [← hy]
    change ψ a = ψ a * ψ (algebraMap F (Adeles F) y)
    rw [hF, mul_one]
  let g : AdeleQuotient F → ℂ :=
    Quotient.lift (s := QuotientAddGroup.leftRel (principalAdeles F)) ψ hrel
  have hg : Continuous g := hc.quotient_lift hrel
  obtain ⟨B, hB⟩ := (isCompact_range hg).isBounded.exists_norm_le
  exact ⟨B, fun x => hB _ ⟨(x : AdeleQuotient F), rfl⟩⟩

/-- A continuous additive character of the adeles that is trivial on `F` is unitary. -/
theorem norm_eq_one_of_trivial (ψ : AddChar (Adeles F) ℂ) (hc : Continuous ψ)
    (hF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (x : Adeles F) :
    ‖ψ x‖ = 1 := by
  obtain ⟨B, hB⟩ := exists_norm_le_of_trivial F ψ hc hF
  have hle : ∀ y, ‖ψ y‖ ≤ 1 := by
    intro y
    by_contra h
    push Not at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    have hy := hB (n • y)
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at hy
    linarith
  have h1 : ψ (-x) * ψ x = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : ‖ψ (-x)‖ * ‖ψ x‖ = 1 := by rw [← norm_mul, h1, norm_one]
  apply le_antisymm (hle x)
  nlinarith [hle (-x), norm_nonneg (ψ (-x)), norm_nonneg (ψ x)]

/-- The hypotheses on `ψ` in `WhittakerExpansionStatement` give a standard additive
character. -/
theorem isStandardAdditiveCharacter_of_continuous (ψ : AddChar (Adeles F) ℂ)
    (hc : Continuous ψ) (hF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (hne : ψ ≠ 1) :
    IsStandardAdditiveCharacter F ψ :=
  ⟨hc, hne, hF, norm_eq_one_of_trivial F ψ hc hF⟩

end Langlands.Global.SmoothWhittakerExpansion
