import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerCharDeriv
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-! # Regularity and unipotent derivatives of complex local Whittaker functions -/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Operator
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean

section Model

variable {r : ℕ} {d : List ComplexCharacterData} {a : ℂˣ}
variable {W : Langlands.GeneralLinear (r + 1) ℂ → ℂ}

private def whittakerRegularFunctions (r : ℕ) (a : ℂˣ) :
    Submodule ℂ (Langlands.GeneralLinear (r + 1) ℂ → ℂ) where
  carrier := {W |
    ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ W ∧
    (∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℂ,
      ∀ g, W (u * g) = complexWhittakerCharacter a u * W g) ∧
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      ∀ g, ‖W g‖ ≤ C * max 1 (complexMatrixHeight g) ^ N}
  zero_mem' := ⟨contMDiff_const, by simp, 0, 0, le_rfl, by simp⟩
  add_mem' := by
    rintro W₁ W₂ ⟨hs₁, hu₁, C₁, N₁, hC₁, hg₁⟩ ⟨hs₂, hu₂, C₂, N₂, hC₂, hg₂⟩
    refine ⟨hs₁.add hs₂, ?_, C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
    · intro u hu g
      simp only [Pi.add_apply, hu₁ u hu g, hu₂ u hu g, mul_add]
    · intro g
      let H := max 1 (complexMatrixHeight g)
      have hH : 1 ≤ H := le_max_left _ _
      change ‖W₁ g + W₂ g‖ ≤ (C₁ + C₂) * H ^ max N₁ N₂
      rw [add_mul]
      exact (norm_add_le _ _).trans (add_le_add
        ((hg₁ g).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hH (le_max_left N₁ N₂)) hC₁))
        ((hg₂ g).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hH (le_max_right N₁ N₂)) hC₂)))
  smul_mem' := by
    rintro c W ⟨hs, hu, C, N, hC, hg⟩
    refine ⟨((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hs,
      ?_, ‖c‖ * C, N, mul_nonneg (norm_nonneg _) hC, ?_⟩
    · intro u h g
      change c * W (u * g) = complexWhittakerCharacter a u * (c * W g)
      rw [hu u h g, mul_left_comm]
    · intro g
      simp only [Pi.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hg g) (norm_nonneg c)

private theorem complexWhittakerModel_le_regularFunctions :
    complexWhittakerModel r d a ≤ whittakerRegularFunctions r a := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  rintro _ ⟨f, rfl⟩
  obtain ⟨C, N, hC⟩ := hB.2.2.1 f
  refine ⟨hB.2.1 f, hB.1 f, max C 0, N, le_max_right _ _, fun g => (hC g).trans ?_⟩
  have hH : 0 ≤ complexMatrixHeight g := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hH (le_max_right _ _) _) (pow_nonneg hH _)
    (le_max_right _ _)

/-- Smoothness of a vector of the complex local Whittaker model. -/
theorem contMDiff_of_mem_complexWhittakerModel (hW : W ∈ complexWhittakerModel r d a) :
    ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ W :=
  (complexWhittakerModel_le_regularFunctions hW).1

/-- Left upper-unipotent covariance in the complex local Whittaker model. -/
theorem complexWhittakerModel_left_equivariant (hW : W ∈ complexWhittakerModel r d a)
    (u : Langlands.GeneralLinear (r + 1) ℂ) (hu : u ∈ GeneralLinear.upperUnipotent (r + 1) ℂ)
    (g : Langlands.GeneralLinear (r + 1) ℂ) :
    W (u * g) = complexWhittakerCharacter a u * W g :=
  (complexWhittakerModel_le_regularFunctions hW).2.1 u hu g

/-- Each vector of the complex local Whittaker model has a polynomial height bound. -/
theorem complexWhittakerModel_moderateGrowth (hW : W ∈ complexWhittakerModel r d a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      ∀ g, ‖W g‖ ≤ C * max 1 (complexMatrixHeight g) ^ N :=
  (complexWhittakerModel_le_regularFunctions hW).2.2

/-- The complex local Whittaker model is stable under right translation by the unitary group. -/
theorem rightTranslation_mem_complexWhittakerModel (hW : W ∈ complexWhittakerModel r d a)
    (k : unitaryCompact ℂ (r + 1)) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℂ)
      (k : Langlands.GeneralLinear (r + 1) ℂ) W ∈ complexWhittakerModel r d a := by
  let T := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℂ)
    (k : Langlands.GeneralLinear (r + 1) ℂ)
  have h : complexWhittakerModel r d a ≤ (complexWhittakerModel r d a).comap T := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    rintro _ ⟨f, rfl⟩
    let f' : Automorphic.complexStandardKFinite (r + 1) d :=
      ⟨_, rightTranslation_mem_kFiniteFunctions_complexStandardModule _ _ f.2 k.2⟩
    change T (B f) ∈ complexWhittakerModel r d a
    rw [← hB.2.2.2.1 k f f' rfl]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f', rfl⟩)
  exact h hW

/-- The complex local Whittaker model is stable under each right Lie derivative. -/
theorem rightDerivative_mem_complexWhittakerModel (hW : W ∈ complexWhittakerModel r d a)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    rightDerivative (matrixModel ℂ (r + 1)) X W ∈ complexWhittakerModel r d a := by
  let V := complexWhittakerModel r d a
  let T := rightDerivativeLinearMap V (fun _ hf => contMDiff_of_mem_complexWhittakerModel hf) X
  have h : V ≤ (V.comap T).map V.subtype := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    rintro _ ⟨f, rfl⟩
    let f' : Automorphic.complexStandardKFinite (r + 1) d :=
      ⟨_, rightDerivative_mem_kFiniteFunctions_complexStandardModule _ _ f.2 X⟩
    have hmem (v : Automorphic.complexStandardKFinite (r + 1) d) : B v ∈ V :=
      Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
    refine ⟨⟨B f, hmem f⟩, ?_, rfl⟩
    change rightDerivative (matrixModel ℂ (r + 1)) X (B f) ∈ V
    rw [← hB.2.2.2.2 X f f' rfl]
    exact hmem f'
  obtain ⟨v, hv, hvW⟩ := h hW
  change rightDerivative (matrixModel ℂ (r + 1)) X (v : _) ∈ V at hv
  rw [show (v : Langlands.GeneralLinear (r + 1) ℂ → ℂ) = W from hvW] at hv
  exact hv

/-- Right differentiation acting on the complex local Whittaker model. -/
def complexWhittakerRightDerivative (r : ℕ) (d : List ComplexCharacterData) (a : ℂˣ)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Module.End ℂ (complexWhittakerModel r d a) :=
  (rightDerivativeLinearMap _ (fun _ hf => contMDiff_of_mem_complexWhittakerModel hf) X).codRestrict _
    (fun W => rightDerivative_mem_complexWhittakerModel W.2 X)

end Model

section CharacterDerivative

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ

private theorem affineUnipotentMatrix (Z : Mat) (hZ : ∀ i j, j ≤ i → Z i j = 0) (t : ℝ) :
    (1 + t • Z).IsUpperTriangular ∧ ∀ i, (1 + t • Z) i i = 1 := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · change j < i at h
    simp [Matrix.add_apply, Matrix.smul_apply, hZ i j h.le, Matrix.one_apply_ne h.ne']
  · simp [Matrix.add_apply, Matrix.smul_apply, hZ i i le_rfl]

private def affineUnipotent (Z : Mat) (hZ : ∀ i j, j ≤ i → Z i j = 0) (t : ℝ) :
    GeneralLinear.upperUnipotent (r + 1) ℂ := by
  have h := affineUnipotentMatrix Z hZ t
  have hd : Matrix.det (1 + t • Z) = 1 := by rw [Matrix.det_of_isUpperTriangular h.1]; simp [h.2]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hd ▸ one_ne_zero), h⟩

/-- Character frequency for a strictly upper triangular matrix in the complex Whittaker model. -/
def complexWhittakerFrequency (a : ℂˣ) (Z : Mat) : ℂ :=
  2 * Real.pi * (Algebra.trace ℝ ℂ ((a : ℂ) *
    ∑ i : Fin r, Z i.castSucc i.succ) : ℂ) * Complex.I

private theorem character_affineUnipotent (a : ℂˣ) (Z : Mat)
    (hZ : ∀ i j, j ≤ i → Z i j = 0) (t : ℝ) :
    complexWhittakerCharacter a (affineUnipotent Z hZ t).val =
      (Real.fourierChar (t * Algebra.trace ℝ ℂ
        ((a : ℂ) * ∑ i : Fin r, Z i.castSucc i.succ)) : ℂ) := by
  change (complexScaledCharacter a).complex
    (∑ i : Fin r, (1 + t • Z) i.castSucc i.succ) = _
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply,
    Matrix.add_apply, Matrix.smul_apply]
  simp only [Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ), zero_add]
  rw [← Finset.smul_sum, mul_smul_comm, map_smul, smul_eq_mul]

/-- The right derivative in the direction conjugate to a strictly upper triangular matrix is
the derivative of the left unipotent character, times the Whittaker function. -/
theorem complexWhittakerModel_unipotent_derivative {d : List ComplexCharacterData} {a : ℂˣ}
    {W : G → ℂ} (hW : W ∈ complexWhittakerModel r d a) (g : G)
    (Z : Mat) (hZ : ∀ i j, j ≤ i → Z i j = 0) :
    rightDerivative (matrixModel ℂ (r + 1)) ((g⁻¹ : G).val * Z * g.val) W g =
      complexWhittakerFrequency a Z * W g := by
  have hs := contMDiff_of_mem_complexWhittakerModel hW
  rw [rightDerivative_eq_fderiv hs]
  rw [← mul_assoc g.val, ← mul_assoc g.val, Units.mul_inv, one_mul]
  let p : ℝ → Mat := fun t => g.val + t • (Z * g.val)
  have hp : HasDerivAt p (Z * g.val) 0 := by
    simpa [p] using ((hasDerivAt_id (0 : ℝ)).smul_const (Z * g.val)).const_add g.val
  have hf := (differentiableAt_unitsExtension hs (Units.isUnit g)).hasFDerivAt
  have hd : HasDerivAt (unitsExtension W ∘ p)
      (fderiv ℝ (unitsExtension W) g.val (Z * g.val)) 0 :=
    hf.comp_hasDerivAt_of_eq 0 hp (by simp [p])
  have heq : (unitsExtension W ∘ p) = fun t : ℝ =>
      (Real.fourierChar (t * Algebra.trace ℝ ℂ
        ((a : ℂ) * ∑ i : Fin r, Z i.castSucc i.succ)) : ℂ) * W g := by
    funext t
    let u := affineUnipotent Z hZ t
    have hu : (u.val * g).val = p t := by
      change (1 + t • Z) * g.val = g.val + t • (Z * g.val)
      rw [add_mul, one_mul, smul_mul_assoc]
    rw [Function.comp_apply, ← hu, unitsExtension_val,
      complexWhittakerModel_left_equivariant hW u.val u.2, character_affineUnipotent]
  rw [heq] at hd
  exact hd.unique ((Langlands.Global.RankinSelbergGlobal.Unfolding.hasDerivAt_fourierChar_mul _).mul_const _)

/-- Iterating the same right derivative iterates the character multiplier. -/
theorem complexWhittakerModel_unipotent_derivative_pow {d : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r d a) (g : G)
    (Z : Mat) (hZ : ∀ i j, j ≤ i → Z i j = 0) (k : ℕ) :
    (((complexWhittakerRightDerivative r d a ((g⁻¹ : G).val * Z * g.val) ^ k) W :
        complexWhittakerModel r d a) : G → ℂ) g =
      complexWhittakerFrequency a Z ^ k * (W : G → ℂ) g := by
  induction k generalizing W with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change rightDerivative (matrixModel ℂ (r + 1)) ((g⁻¹ : G).val * Z * g.val)
      (((complexWhittakerRightDerivative r d a ((g⁻¹ : G).val * Z * g.val) ^ k) W :
        complexWhittakerModel r d a) : G → ℂ) g = _
    rw [complexWhittakerModel_unipotent_derivative (Submodule.coe_mem _) g Z hZ, ih,
      pow_succ', mul_assoc]

end CharacterDerivative

end Langlands.Global.RankinSelbergGlobal
