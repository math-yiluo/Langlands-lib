import Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourier
import Langlands.AllField.HarmonicAnalysis.RectangularFourierUnimodularTranslate
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffTests
/-! # Fourier covariance of actual supercuspidal cutoff coefficients -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient
open Langlands.AllField.GodementJacquet

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicRectangularHaarScaling padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {d : ℕ} (hd : 0 < d)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem supercuspidalCutoffMatrixTest_right :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear d F) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V)
      (g : GeneralLinear d F), T.determinantNorm d g = 1 →
      ∀ A : Matrix (Fin d) (Fin d) F,
        supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ (ρ g v) A =
          supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v (A * g.val) := by
  let := T.topology
  intro ρ hρ ℓ hℓ v g hg A
  by_cases hA : IsUnit A
  · obtain ⟨a, rfl⟩ := hA
    by_cases ha : T.determinantNorm d a = 1
    · have hag : T.determinantNorm d (a * g) = 1 := by
        rw [map_mul, ha, hg, mul_one]
      rw [← Units.val_mul,
        supercuspidalCutoffMatrixTest_apply T hd ρ hρ ℓ hℓ (ρ g v) ⟨a, ha⟩,
        supercuspidalCutoffMatrixTest_apply T hd ρ hρ ℓ hℓ v ⟨a * g, hag⟩]
      simp
    · have hag : T.determinantNorm d (a * g) ≠ 1 := by
        simpa only [map_mul, hg, mul_one] using ha
      rw [supercuspidalCutoffMatrixTest_apply_of_not_mem T hd ρ hρ ℓ hℓ (ρ g v) a ha,
        ← Units.val_mul,
        supercuspidalCutoffMatrixTest_apply_of_not_mem T hd ρ hρ ℓ hℓ v (a * g) hag]
  · have hAg : ¬ IsUnit (A * g.val) := by
      intro h
      apply hA
      have he : A * g.val * (g⁻¹ : GeneralLinear d F).val = A := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.mul_one]
      exact he ▸ h.mul (g⁻¹).isUnit
    rw [supercuspidalCutoffMatrixTest_singular T hd ρ hρ ℓ hℓ (ρ g v) A hA,
      supercuspidalCutoffMatrixTest_singular T hd ρ hρ ℓ hℓ v _ hAg]

/-- The Fourier integral of the actual cutoff is covariant under every
determinant-unit right translate of the representation vector. -/
theorem supercuspidalCutoffMatrixTest_fourier_right :
    letI := T.topology
    letI := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (ρ : Representation ℂ (GeneralLinear d F) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V)
      (g : GeneralLinear d F), T.determinantNorm d g = 1 →
      ∀ A : Matrix (Fin d) (Fin d) F,
        rectangularFourierIntegral ψ ν
            (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ (ρ g v)) A =
          rectangularFourierIntegral ψ ν
            (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v)
            (A * (inverseTranspose d F g).val) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ ν ρ hρ ℓ hℓ v g hg A
  have he : (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ (ρ g v) :
      Matrix (Fin d) (Fin d) F → ℂ) =
      fun X => supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v (1 * X * g.val) := by
    funext X
    simpa only [Matrix.one_mul] using
      supercuspidalCutoffMatrixTest_right T hd ρ hρ ℓ hℓ v g hg X
  rw [he]
  simpa only [Units.val_one, Matrix.one_mul, map_one] using
    rectangularFourierIntegral_comp_mul_mul T ψ ν 1 g (map_one _) hg
      (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v) A

/-- Actual Fourier evaluation of the cutoff as a linear functional in its vector. -/
def supercuspidalCutoffFourierEvaluation :
    letI := T.topology
    letI := borel F
    ∀ (_ψ : UnitaryAdditiveCharacter F) (_ν : AdditiveHaarMeasure F)
      (ρ : Representation ℂ (GeneralLinear d F) V)
      (_hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (_hℓ : IsSmoothVector ρ.dual ℓ),
      Matrix (Fin d) (Fin d) F → V →ₗ[ℂ] ℂ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ ν ρ hρ ℓ hℓ A
  exact
    { toFun := fun w => rectangularFourierTransform ψ ν
        (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ w) A
      map_add' := by
        intro w z
        simp only [map_add]
        rfl
      map_smul' := by
        intro c w
        simp only [map_smul]
        rfl }

/-- A Fourier evaluation fixed by a subgroup with zero Jacquet quotient is zero.
No averaging or quotient measure is used. -/
theorem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer :
    letI := T.topology
    letI := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (ρ : Representation ℂ (GeneralLinear d F) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ)
      (N : Subgroup (GeneralLinear d F)),
      Subsingleton (Jacquet.Coinvariants ρ N) →
      (∀ g ∈ N, T.determinantNorm d g = 1) →
      ∀ A : Matrix (Fin d) (Fin d) F,
      (∀ g ∈ N, A * (inverseTranspose d F g).val = A) →
      ∀ v : V, rectangularFourierIntegral ψ ν
        (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v) A = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ ν ρ hρ ℓ hℓ N hN hnorm A hA v
  let L := supercuspidalCutoffFourierEvaluation T hd ψ ν ρ hρ ℓ hℓ A
  have hL (g : N) : L ∘ₗ ρ g = L := by
    ext w
    change rectangularFourierIntegral ψ ν
        (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ (ρ g.val w)) A =
      rectangularFourierIntegral ψ ν
        (supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ w) A
    rw [supercuspidalCutoffMatrixTest_fourier_right T hd ψ ν ρ hρ ℓ hℓ w
        g.val (hnorm g.val g.property), hA g.val g.property]
  let := hN
  have hz : Jacquet.mk ρ N v = 0 := Subsingleton.elim _ _
  have h := congrArg (Jacquet.lift ρ N L hL) hz
  change L v = 0
  simpa only [Jacquet.lift_mk, map_zero] using h

/-- Every conjugate block radical has determinant norm one. -/
theorem determinantNorm_eq_one_of_mem_conjugateUnipotent
    (B : BlockShape d) (g : GeneralLinear d F)
    {u : GeneralLinear d F} (hu : u ∈ B.conjugateUnipotent g) :
    T.determinantNorm d u = 1 := by
  rcases hu with ⟨u, hu, rfl⟩
  rcases hu with ⟨v, hv, rfl⟩
  have hv' : B.leviProjection F v = 1 := hv
  have hdet : determinant v.val = 1 := by
    rw [determinant_blockParabolic, hv']
    simp
  change T.determinantNorm d (g * v.val * g⁻¹) = 1
  change T.normalizedAbsUnits (determinant (g * v.val * g⁻¹)) = 1
  simp [map_mul, hdet]

end Langlands.AllField.GodementJacquet
