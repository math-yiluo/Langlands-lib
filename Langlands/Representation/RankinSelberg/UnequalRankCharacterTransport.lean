import Langlands.Representation.RankinSelberg.CharacterChangeBlocks

/-!
# Actual unequal-rank Whittaker data under change of additive character
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The row scaling is a continuous linear equivalence for the product topology. -/
def characterChangeRectangularContinuous (a : Fˣ) (j n : ℕ) :
    Matrix (Fin j) (Fin (n + 1)) F ≃L[F] Matrix (Fin j) (Fin (n + 1)) F where
  toLinearEquiv := characterChangeRectangular a j n
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro l
    exact continuous_const.mul ((continuous_apply l).comp (continuous_apply i))
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro l
    exact continuous_const.mul ((continuous_apply l).comp (continuous_apply i))

variable (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (n j k : ℕ)

/-- Corrected large-rank Whittaker function: `g ↦ W(D g R⁻¹)`. -/
def unequalRankCharacterChangeFunction :
    WhittakerFunctions ψ (n + (j + k + 1)) →ₗ[ℂ]
      WhittakerFunctions (ψ.scale a) (n + (j + k + 1)) :=
  (functionRepresentation (upperUnipotent (n + (j + k + 1) + 1) F)
    (standardCharacter (ψ.scale a) (n + (j + k + 1)))
      (characterChangeBlockCorrection a n (j + k + 1))⁻¹).comp
        (characterChangeFunction ψ (n + (j + k + 1)) a)

@[simp] theorem unequalRankCharacterChangeFunction_apply
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (g : Langlands.GeneralLinear (n + (j + k + 1) + 1) F) :
    (unequalRankCharacterChangeFunction ψ a n j k W).val g =
      W.val (characterChangeElement a (n + (j + k + 1)) * g *
        (characterChangeBlockCorrection a n (j + k + 1))⁻¹) := by
  change W.val (characterChangeElement a (n + (j + k + 1)) *
      (g * (characterChangeBlockCorrection a n (j + k + 1))⁻¹)) = _
  rw [mul_assoc]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)

/-- The corrected function is the coefficient of the transported functional
and the vector translated by the fixed right correction's inverse. -/
theorem unequalRankCharacterChangeFunction_coefficient
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (v : V) :
    coefficientMap π (characterChangeFunctional ψ π a ℓ)
        (π (characterChangeBlockCorrection a n (j + k + 1))⁻¹ v) =
      unequalRankCharacterChangeFunction ψ a n j k (coefficientMap π ℓ v) := by
  ext g
  rw [unequalRankCharacterChangeFunction_apply]
  change ℓ.val (π (characterChangeElement a (n + (j + k + 1)))
      (π g (π (characterChangeBlockCorrection a n (j + k + 1))⁻¹ v))) =
    ℓ.val (π (characterChangeElement a (n + (j + k + 1)) * g *
      (characterChangeBlockCorrection a n (j + k + 1))⁻¹) v)
  simp only [map_mul, Module.End.mul_apply]

/-- The corrected transport maps each actual coefficient image onto the image
of the transported functional. -/
theorem unequalRankCharacterChangeFunction_coefficientModel
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) :
    (coefficientModel π (characterChangeFunctional ψ π a ℓ)).toSubmodule =
      (coefficientModel π ℓ).toSubmodule.map
        (unequalRankCharacterChangeFunction ψ a n j k) := by
  ext W
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨coefficientMap π ℓ (π (characterChangeBlockCorrection a n (j + k + 1)) v),
      ⟨_, rfl⟩, ?_⟩
    rw [← unequalRankCharacterChangeFunction_coefficient]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rfl
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨π (characterChangeBlockCorrection a n (j + k + 1))⁻¹ v,
      unequalRankCharacterChangeFunction_coefficient ψ a n j k π ℓ v⟩

/-- The intrinsic coefficient set is exactly the image under the corrected
transport; the source functional and vector are recovered explicitly. -/
theorem whittakerSet_unequalRankCharacterChange :
    whittakerSet (ψ.scale a) (n + (j + k + 1)) π =
      unequalRankCharacterChangeFunction ψ a n j k ''
        whittakerSet ψ (n + (j + k + 1)) π := by
  ext W
  constructor
  · rintro ⟨ℓ, v, rfl⟩
    obtain ⟨ℓ₀, rfl⟩ := (characterChangeFunctionalEquiv ψ π a).surjective ℓ
    refine ⟨coefficientMap π ℓ₀ (π (characterChangeBlockCorrection a n (j + k + 1)) v),
      ⟨ℓ₀, _, rfl⟩, ?_⟩
    rw [← unequalRankCharacterChangeFunction_coefficient]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rfl
  · rintro ⟨_, ⟨ℓ, v, rfl⟩, rfl⟩
    exact ⟨characterChangeFunctional ψ π a ℓ,
      π (characterChangeBlockCorrection a n (j + k + 1))⁻¹ v,
      unequalRankCharacterChangeFunction_coefficient ψ a n j k π ℓ v⟩

/-- The actual quotient integrand identity. The determinant exponent retains
the half-gap shift from the unequal-rank integral. -/
theorem unequalRankIntegrand_characterChange (abv : AbsoluteValue F ℝ)
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k W W' s
      (characterChangeRectangular a j n x) (characterChangeQuotient a n q) =
    determinantWeight abv (characterChangeElement a n)
      (s - ((j + k + 1 : ℕ) : ℂ) / 2) *
      unequalRankIntegrand (ψ.scale a) abv j k
        (unequalRankCharacterChangeFunction ψ a n j k W)
        (characterChangeInverseFunction ψ n a W') s x q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [characterChangeQuotient_mk, unequalRankIntegrand_mk,
      unequalRankCharacterChangeFunction_apply, characterChangeInverseFunction_apply,
      unequalRankMatrix_characterChange, mul_inv_cancel_right, determinantWeight_mul]
    ring

end Langlands.RankinSelberg
