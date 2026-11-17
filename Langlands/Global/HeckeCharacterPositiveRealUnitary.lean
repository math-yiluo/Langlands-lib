import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.Global.PositiveRealIdeles

/-!
# Hecke characters trivial on the positive real ideles are unitary

For a number field `F`, a continuous character `χ : F^× \ 𝔸_F^× → ℂ^×` (a `HeckeCharacter F`)
that is trivial on the classes of the positive real ideles `PositiveRealIdeles.full F a` (the
group `A_(G_m)` of Getz–Hahn, display (2.20)) is unitary:
`HeckeCharacter.isUnitary_of_positiveRealIdeles`.

The proof uses the published lemma `HeckeEulerProduct.norm_eq_one_of_ideleClass_eq_one`
(`‖χ‖ = 1` on the idele classes of absolute value `1`). See the paired Markdown.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open NumberField
open scoped NNReal

variable {F : Type u} [Field F] [NumberField F]

/-- **Hecke characters trivial on `A_(G_m)` are unitary.** If a continuous character `χ` of the
idele class group is trivial on the classes of the positive real ideles
`PositiveRealIdeles.full F a` (the same positive real `a` at every infinite place, `1` at every
finite place), then `‖χ(c)‖ = 1` for every idele class `c`.

For an idele `z` with absolute value `s`, the idele `z ^ d * (PositiveRealIdeles.full F s)⁻¹`,
`d = [F : ℚ]`, has absolute value `s ^ d * (s ^ d)⁻¹ = 1`, so `‖χ(z)‖ ^ d = 1`. -/
theorem isUnitary_of_positiveRealIdeles (χ : HeckeCharacter F)
    (hχ : ∀ a : ℝ≥0ˣ, χ (ideleClassMap F (PositiveRealIdeles.full F a)) = 1) :
    χ.IsUnitary := by
  intro c
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective c
  have hy : IdeleAbsoluteValue.ideleClass F (ideleClassMap F (z ^ Module.finrank ℚ F *
      (PositiveRealIdeles.full F (IdeleAbsoluteValue.full F z))⁻¹)) = 1 := by
    rw [IdeleAbsoluteValue.ideleClass_class, map_mul, map_pow, map_inv,
      PositiveRealIdeles.absoluteValue_full]
    exact mul_inv_cancel _
  have h1 := HeckeEulerProduct.norm_eq_one_of_ideleClass_eq_one χ hy
  simp only [map_mul, map_pow, map_inv, hχ, inv_one, mul_one, Units.val_pow_eq_pow_val,
    norm_pow] at h1
  have hn : Module.finrank ℚ F ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  change ‖(χ (ideleClassMap F z) : ℂ)‖ = 1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1

end Langlands.Global.HeckeCharacter
