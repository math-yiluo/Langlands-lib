import Langlands.Global.ArchimedeanGL
import Langlands.Global.AdelicGL

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A concrete height controlling both the matrix and its inverse. -/
def matrixHeight (g : InfiniteAdelicGL K n) : ℝ :=
  max 1 (max ‖(archimedeanGLCoordinates K n g).val‖
    ‖(archimedeanGLCoordinates K n g).inv‖)

theorem one_le_matrixHeight (g : InfiniteAdelicGL K n) : 1 ≤ matrixHeight K n g :=
  le_max_left _ _

theorem matrixHeight_nonneg (g : InfiniteAdelicGL K n) : 0 ≤ matrixHeight K n g :=
  le_trans zero_le_one (one_le_matrixHeight K n g)

theorem norm_val_le_matrixHeight (g : InfiniteAdelicGL K n) :
    ‖(archimedeanGLCoordinates K n g).val‖ ≤ matrixHeight K n g :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem norm_inv_le_matrixHeight (g : InfiniteAdelicGL K n) :
    ‖(archimedeanGLCoordinates K n g).inv‖ ≤ matrixHeight K n g :=
  le_trans (le_max_right _ _) (le_max_right _ _)

@[simp]
theorem matrixHeight_inv (g : InfiniteAdelicGL K n) :
    matrixHeight K n g⁻¹ = matrixHeight K n g := by
  simp only [matrixHeight, map_inv]
  change max 1 (max ‖(archimedeanGLCoordinates K n g).inv‖
    ‖(archimedeanGLCoordinates K n g).val‖) = _
  rw [max_comm ‖(archimedeanGLCoordinates K n g).inv‖]

theorem matrixHeight_mul_le (g h : InfiniteAdelicGL K n) :
    matrixHeight K n (g * h) ≤ matrixHeight K n g * matrixHeight K n h := by
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_matrixHeight K n g)
      (one_le_matrixHeight K n h)
  · apply max_le
    · calc
        ‖(archimedeanGLCoordinates K n (g * h)).val‖ =
            ‖(archimedeanGLCoordinates K n g).val *
              (archimedeanGLCoordinates K n h).val‖ := by rw [map_mul]; rfl
        _ ≤ ‖(archimedeanGLCoordinates K n g).val‖ *
              ‖(archimedeanGLCoordinates K n h).val‖ := norm_mul_le _ _
        _ ≤ matrixHeight K n g * matrixHeight K n h :=
          mul_le_mul (norm_val_le_matrixHeight K n g) (norm_val_le_matrixHeight K n h)
            (norm_nonneg _) (matrixHeight_nonneg K n g)
    · calc
        ‖(archimedeanGLCoordinates K n (g * h)).inv‖ =
            ‖(archimedeanGLCoordinates K n h).inv *
              (archimedeanGLCoordinates K n g).inv‖ := by rw [map_mul]; rfl
        _ ≤ ‖(archimedeanGLCoordinates K n h).inv‖ *
              ‖(archimedeanGLCoordinates K n g).inv‖ := norm_mul_le _ _
        _ ≤ matrixHeight K n h * matrixHeight K n g :=
          mul_le_mul (norm_inv_le_matrixHeight K n h) (norm_inv_le_matrixHeight K n g)
            (norm_nonneg _) (matrixHeight_nonneg K n h)
        _ = matrixHeight K n g * matrixHeight K n h := mul_comm _ _

theorem continuous_matrixHeight : Continuous (matrixHeight K n) := by
  have hv : Continuous (fun g : InfiniteAdelicGL K n =>
      (archimedeanGLCoordinates K n g).val) :=
    Units.continuous_val.comp (archimedeanGLCoordinates K n).continuous
  have hi : Continuous (fun g : InfiniteAdelicGL K n =>
      (archimedeanGLCoordinates K n g).inv) :=
    Units.continuous_val.comp ((archimedeanGLCoordinates K n).continuous.inv)
  exact continuous_const.max (hv.norm.max hi.norm)

/-- Polynomial growth for this concrete matrix/inverse height. -/
def HasPolynomialGrowth (f : InfiniteAdelicGL K n → ℂ) : Prop :=
  ∃ (C : ℝ), 0 ≤ C ∧ ∃ (d : ℕ), ∀ g, ‖f g‖ ≤ C * matrixHeight K n g ^ d

variable {K n}

theorem HasPolynomialGrowth.zero : HasPolynomialGrowth K n (0 : InfiniteAdelicGL K n → ℂ) := by
  exact ⟨0, le_refl 0, 0, by simp⟩

theorem HasPolynomialGrowth.const (c : ℂ) :
    HasPolynomialGrowth K n (fun _ : InfiniteAdelicGL K n => c) := by
  exact ⟨‖c‖, norm_nonneg _, 0, by simp⟩

theorem HasPolynomialGrowth.add {f h : InfiniteAdelicGL K n → ℂ}
    (hf : HasPolynomialGrowth K n f) (hh : HasPolynomialGrowth K n h) :
    HasPolynomialGrowth K n (f + h) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hh⟩ := hh
  refine ⟨C + D, add_nonneg hC hD, max d e, ?_⟩
  intro g
  calc
    ‖(f + h) g‖ ≤ ‖f g‖ + ‖h g‖ := norm_add_le _ _
    _ ≤ C * matrixHeight K n g ^ d + D * matrixHeight K n g ^ e := add_le_add (hf g) (hh g)
    _ ≤ C * matrixHeight K n g ^ max d e + D * matrixHeight K n g ^ max d e :=
      add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (one_le_matrixHeight K n g) (le_max_left d e)) hC)
        (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (one_le_matrixHeight K n g) (le_max_right d e)) hD)
    _ = (C + D) * matrixHeight K n g ^ max d e := (add_mul _ _ _).symm

theorem HasPolynomialGrowth.smul {f : InfiniteAdelicGL K n → ℂ}
    (hf : HasPolynomialGrowth K n f) (c : ℂ) : HasPolynomialGrowth K n (c • f) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, d, ?_⟩
  intro g
  calc
    ‖(c • f) g‖ = ‖c‖ * ‖f g‖ := norm_mul _ _
    _ ≤ ‖c‖ * (C * matrixHeight K n g ^ d) :=
      mul_le_mul_of_nonneg_left (hf g) (norm_nonneg _)
    _ = (‖c‖ * C) * matrixHeight K n g ^ d := (mul_assoc _ _ _).symm

theorem HasPolynomialGrowth.rightTranslate {f : InfiniteAdelicGL K n → ℂ}
    (hf : HasPolynomialGrowth K n f) (h : InfiniteAdelicGL K n) :
    HasPolynomialGrowth K n (fun g => f (g * h)) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨C * matrixHeight K n h ^ d,
    mul_nonneg hC (pow_nonneg (matrixHeight_nonneg K n h) d), d, ?_⟩
  intro g
  calc
    ‖f (g * h)‖ ≤ C * matrixHeight K n (g * h) ^ d := hf _
    _ ≤ C * (matrixHeight K n g * matrixHeight K n h) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (matrixHeight_nonneg K n _) (matrixHeight_mul_le K n g h) d) hC
    _ = (C * matrixHeight K n h ^ d) * matrixHeight K n g ^ d := by rw [mul_pow]; ring

theorem hasPolynomialGrowth_rightTranslate_iff (f : InfiniteAdelicGL K n → ℂ)
    (h : InfiniteAdelicGL K n) :
    HasPolynomialGrowth K n (fun g => f (g * h)) ↔ HasPolynomialGrowth K n f := by
  constructor
  · intro hf
    simpa only [inv_mul_cancel_right] using hf.rightTranslate h⁻¹
  · exact fun hf => hf.rightTranslate h

variable (K n)

/-- The actual complex subspace of functions with polynomial matrix growth. -/
def polynomialGrowthFunctions : Submodule ℂ (InfiniteAdelicGL K n → ℂ) where
  carrier := {f | HasPolynomialGrowth K n f}
  zero_mem' := HasPolynomialGrowth.zero
  add_mem' := HasPolynomialGrowth.add
  smul_mem' c _ hf := hf.smul c

@[simp]
theorem mem_polynomialGrowthFunctions (f : InfiniteAdelicGL K n → ℂ) :
    f ∈ polynomialGrowthFunctions K n ↔ HasPolynomialGrowth K n f := Iff.rfl

end Langlands.Global.ArchimedeanGL
