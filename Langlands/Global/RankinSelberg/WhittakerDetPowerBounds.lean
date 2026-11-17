import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerWords

/-! # Determinant power bounds for Whittaker functions and derivative words -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

local instance detPowerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- Whittaker averaging preserves a global determinant power bound. -/
theorem norm_whittaker_le_of_detPower {r : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (f : Points F (r + 1) → ℂ)
    (β B : ℝ) (hB : ∀ g : Points F (r + 1), ‖f g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (g : Points F (r + 1)) :
    ‖whittaker F r ψ f g‖ ≤ B * detNorm F (r + 1) g ^ β := by
  refine norm_whittaker_le F ψ hψ f g _ fun n => ?_
  simpa only [detNorm_mul, detNorm_unipotent, one_mul] using hB ((n : Points F (r + 1)) * g)

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}

/-- A common determinant exponent bounds all powers of a derivative whose matrix
entries are bounded, using one constant independent of the derivative matrix,
the adelic point and the standard additive character. -/
theorem exists_norm_whittaker_pow_le_of_detPower
    (hV : WhittakerDecayClass F r V R) (β : ℝ)
    (hβ : ∀ f : V, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
      ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (K : ℕ) (f : V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ψ : AddChar (Adeles F) ℂ),
      IsStandardAdditiveCharacter F ψ →
      ∀ (Z : ArchimedeanMatrix F (r + 1)) (A : ℝ),
        (∀ a b, ‖Z a b‖ ≤ A) → ∀ g : Points F (r + 1),
          ‖whittaker F r ψ (((R Z) ^ K) f : Points F (r + 1) → ℂ) g‖ ≤
            (coordConst F * A) ^ K * B * detNorm F (r + 1) g ^ β := by
  classical
  choose b hb0 hb using fun l : Fin K → EntryIndex F (r + 1) =>
    hβ (entryWord F (R := R) K l f)
  refine ⟨∑ l, b l, Finset.sum_nonneg (fun l _ => hb0 l), ?_⟩
  intro ψ hψ Z A hA g
  have hA0 : 0 ≤ A := (norm_nonneg (Z 0 0)).trans (hA 0 0)
  calc
    ‖whittaker F r ψ (((R Z) ^ K) f : Points F (r + 1) → ℂ) g‖ ≤
        (coordConst F * A) ^ K *
          ∑ l : Fin K → EntryIndex F (r + 1),
            ‖whittaker F r ψ
              ((entryWord F (R := R) K l f : V) : Points F (r + 1) → ℂ) g‖ :=
      norm_whittaker_pow_le F hV ψ hψ Z hA K f g
    _ ≤ (coordConst F * A) ^ K *
        ∑ l : Fin K → EntryIndex F (r + 1), b l * detNorm F (r + 1) g ^ β :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun l _ =>
          norm_whittaker_le_of_detPower F ψ hψ _ β (b l) (hb l) g)
        (pow_nonneg (mul_nonneg (coordConst_nonneg F) hA0) K)
    _ = (coordConst F * A) ^ K * (∑ l, b l) * detNorm F (r + 1) g ^ β := by
      rw [← Finset.sum_mul, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.Unfolding
