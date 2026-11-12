import Langlands.Global.IdeleNormAbsoluteValue
import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Conjugate-inverse Hecke characters of CM fields are unitary

On a CM field `K`, the complex conjugation `c` of the idele class group preserves the normalized
idelic absolute value. A Hecke character `χ` with `χ ∘ c = χ⁻¹` (Harris's `χ = χ⁻¹ ∘ c`) is
therefore unitary: `|χ|` is trivial on norm-one idele classes, so `|χ ∘ c| = |χ|`, while
`|χ ∘ c| = |χ|⁻¹`.
-/

noncomputable section

universe u

namespace Langlands.Global

open NumberField
open scoped NNReal
open AdelicFunctoriality

namespace HeckeConjugateInverse

variable {K : Type u} [Field K] [NumberField K] [IsCMField K]

/-- Complex conjugation fixes the positive real scalar ideles. -/
theorem ideleEquiv_complexConj_positiveReal (a : ℝ≥0ˣ) :
    ideleEquiv (IsCMField.complexConj K).toRingEquiv (PositiveRealIdeles.full K a) =
      PositiveRealIdeles.full K a := by
  apply Units.ext
  apply Prod.ext
  · funext p
    apply (InfinitePlace.Completion.extensionEmbedding p).injective
    rw [ideleComplexConj_infinite_coordinate, PositiveRealIdeles.extensionEmbedding_full]
    exact Complex.conj_ofReal _
  · change finiteAdeleEquiv _ (PositiveRealIdeles.full K a).val.2 =
      (PositiveRealIdeles.full K a).val.2
    rw [show (PositiveRealIdeles.full K a).val.2 = 1 from rfl, map_one]

/-- Complex conjugation preserves the normalized idelic absolute value. -/
theorem full_ideleEquiv_complexConj (x : Ideles K) :
    IdeleAbsoluteValue.full K (ideleEquiv (IsCMField.complexConj K).toRingEquiv x) =
      IdeleAbsoluteValue.full K x := by
  have heq : (IdeleAbsoluteValue.full K).comp
      (ContinuousMonoidHom.toContinuousMonoidHom
        (ideleEquiv (IsCMField.complexConj K).toRingEquiv)) = IdeleAbsoluteValue.full K := by
    apply IdeleAbsoluteValue.eq_of_positiveRealIdeles
    · intro a
      change IdeleAbsoluteValue.full K
        (ideleEquiv (IsCMField.complexConj K).toRingEquiv (IdeleGroup.unitEmbedding (𝓞 K) K a)) = 1
      rw [ideleEquiv_diagonal]
      exact IdeleAbsoluteValue.full_diagonalUnits K _
    · intro a
      change IdeleAbsoluteValue.full K
        (ideleEquiv (IsCMField.complexConj K).toRingEquiv (PositiveRealIdeles.full K a)) = _
      rw [ideleEquiv_complexConj_positiveReal]
  exact DFunLike.congr_fun heq x

/-- The absolute value of a Hecke character, as a continuous character of the ideles with
values in the positive reals. -/
def absCharacter (χ : HeckeCharacter K) : Ideles K →ₜ* ℝ≥0ˣ :=
  { toMonoidHom := (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom).comp
      (χ.comp (ideleClassMap K)).toMonoidHom
    continuous_toFun :=
      (Continuous.units_map _ continuous_nnnorm).comp (χ.comp (ideleClassMap K)).continuous }

omit [IsCMField K] in
theorem coe_absCharacter (χ : HeckeCharacter K) (x : Ideles K) :
    ((absCharacter χ x : ℝ≥0) : ℝ) = ‖(χ (ideleClassMap K x) : ℂ)‖ := rfl

/-- **A Hecke character `χ` of a CM field with `χ ∘ c = χ⁻¹` is unitary.** -/
theorem isUnitary_of_isConjugateInverse (χ : HeckeCharacter K)
    (hχ : Harris.IsConjugateInverse χ) : χ.IsUnitary := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  set x' := ideleEquiv (IsCMField.complexConj K).toRingEquiv x
  have hprinc : ∀ a : Kˣ, absCharacter χ (diagonalUnits K a) = 1 := by
    intro a
    apply Units.ext
    apply NNReal.eq
    rw [coe_absCharacter]
    have : ideleClassMap K (diagonalUnits K a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    rw [this, map_one]
    simp
  have hfull : IdeleAbsoluteValue.full K (x' * x⁻¹) = 1 := by
    rw [map_mul, map_inv, full_ideleEquiv_complexConj, mul_inv_cancel]
  have hone := IdeleAbsoluteValue.apply_eq_one_of_full_eq_one K (absCharacter χ) hprinc _ hfull
  rw [map_mul, map_inv, mul_inv_eq_one] at hone
  have hr : ‖(χ (ideleClassMap K x') : ℂ)‖ = ‖(χ (ideleClassMap K x) : ℂ)‖ := by
    rw [← coe_absCharacter, ← coe_absCharacter, hone]
  have hc : ideleClassMap K x' = ideleClassComplexConj (ideleClassMap K x) := rfl
  rw [hc, hχ, Units.val_inv_eq_inv_val, norm_inv] at hr
  set r := ‖(χ (ideleClassMap K x) : ℂ)‖ with hrdef
  have hpos : 0 < r := norm_pos_iff.mpr (Units.ne_zero _)
  have hsq : r⁻¹ * r = 1 := inv_mul_cancel₀ hpos.ne'
  rw [hr] at hsq
  change r = 1
  nlinarith [hsq, hpos]

end HeckeConjugateInverse

end Langlands.Global
