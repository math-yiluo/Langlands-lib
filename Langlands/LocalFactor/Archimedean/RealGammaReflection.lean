import Langlands.LocalFactor.Archimedean.Definitions
import Mathlib.Tactic

/-! # Reflection identities for the real principal-series Gamma factors -/

noncomputable section

namespace Langlands.LocalFactor.Archimedean.RealGammaReflection

open Complex

local notation "denR" => gammaReal.denominator
local notation "denC" => gammaComplex.denominator

/-- Inverse normalized Gamma ratio for a real character of parity `e`, at a variable
which already includes the exponent of the character. -/
def characterRatio (e : Fin 2) (z : ℂ) : ℂ :=
  (-I) ^ e.val * denR (1 - z + (e.val : ℂ)) / denR (z + (e.val : ℂ))

/-- Inverse normalized Gamma ratio for a real induced block of absolute weight `k`. -/
def inducedRatio (k : ℕ) (z : ℂ) : ℂ :=
  (-I) ^ (k + 1) * denC (1 - z + (k : ℂ) / 2) / denC (z + (k : ℂ) / 2)

/-- The parity at the positive exponent of the two position characters of a real
induced block. -/
def positionParity (k : ℕ) : Fin 2 := Fin.ofNat 2 k + 1

private theorem parity_add (m n : ℕ) :
    Fin.ofNat 2 (m + n) = Fin.ofNat 2 m + Fin.ofNat 2 n := by
  apply Fin.ext
  exact Nat.add_mod m n 2

private def signedTrig (e : Fin 2) (z : ℂ) : ℂ :=
  if e = 0 then cos (Real.pi * z / 2) else (-I) * sin (Real.pi * z / 2)

@[simp] private theorem signedTrig_zero (z : ℂ) :
    signedTrig 0 z = cos (Real.pi * z / 2) := rfl

@[simp] private theorem signedTrig_one (z : ℂ) :
    signedTrig 1 z = (-I) * sin (Real.pi * z / 2) := rfl

private theorem denC_eq (z : ℂ) : denC z = denR z * denR (z + 1) := by
  change (Gammaℂ z)⁻¹ = (Gammaℝ z)⁻¹ * (Gammaℝ (z + 1))⁻¹
  rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv]

private theorem denR_reflection_even (z : ℂ) :
    denR (1 - z) * denR (z + 1) = cos (Real.pi * z / 2) := by
  change (Gammaℝ (1 - z))⁻¹ * (Gammaℝ (z + 1))⁻¹ = _
  rw [← mul_inv, add_comm z 1, Gammaℝ_one_sub_mul_Gammaℝ_one_add, inv_inv]

private theorem denR_reflection_odd (z : ℂ) :
    denR z * denR (2 - z) = sin (Real.pi * z / 2) := by
  convert denR_reflection_even (1 - z) using 1
  · ring_nf
  · rw [show (Real.pi : ℂ) * (1 - z) / 2 = Real.pi / 2 - Real.pi * z / 2 by ring,
      cos_pi_div_two_sub]

private theorem characterRatio_eq (e : Fin 2) (z : ℂ) (hz : denC z ≠ 0) :
    characterRatio e z = signedTrig e z / denC z := by
  rw [denC_eq] at hz
  have hz₀ := (mul_ne_zero_iff.mp hz).1
  have hz₁ := (mul_ne_zero_iff.mp hz).2
  fin_cases e
  · change characterRatio 0 z = signedTrig 0 z / denC z
    simp only [characterRatio, Fin.val_zero, Nat.cast_zero, pow_zero, add_zero, one_mul,
      signedTrig_zero, denC_eq]
    rw [div_eq_div_iff hz₀ hz, ← denR_reflection_even]
    ring
  · change characterRatio 1 z = signedTrig 1 z / denC z
    simp only [characterRatio, Fin.val_one, Nat.cast_one, pow_one, signedTrig_one, denC_eq]
    rw [show 1 - z + 1 = 2 - z by ring, div_eq_div_iff hz₁ hz, ← denR_reflection_odd]
    ring

private theorem signedTrig_add_one (e : Fin 2) (z : ℂ) :
    signedTrig e (z + 1) = (-I) * signedTrig (e + 1) z := by
  have h : (Real.pi : ℂ) * (z + 1) / 2 = Real.pi * z / 2 + Real.pi / 2 := by ring
  fin_cases e
  · change signedTrig 0 (z + 1) = (-I) * signedTrig 1 z
    rw [signedTrig_zero, h, cos_add_pi_div_two, signedTrig_one,
      ← mul_assoc, neg_mul_neg, I_mul_I, neg_one_mul]
  · change signedTrig 1 (z + 1) = (-I) * signedTrig 0 z
    rw [signedTrig_one, h, sin_add_pi_div_two, signedTrig_zero]

private theorem signedTrig_add_nat (e : Fin 2) (z : ℂ) (k : ℕ) :
    signedTrig e (z + (k : ℂ)) = (-I) ^ k * signedTrig (e + Fin.ofNat 2 k) z := by
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, signedTrig_add_one, ih, pow_succ',
      parity_add, mul_assoc, add_right_comm, add_assoc]
    rfl

private theorem signedTrig_mul_toggle (e : Fin 2) (z : ℂ) :
    signedTrig e z * signedTrig (e + 1) z = signedTrig 0 z * signedTrig 1 z := by
  fin_cases e
  · rfl
  · change signedTrig 1 z * signedTrig 0 z = signedTrig 0 z * signedTrig 1 z
    exact mul_comm _ _

theorem positionParity_add (k : ℕ) :
    positionParity k + Fin.ofNat 2 k = 1 := by
  have h (p : Fin 2) : p + p = 0 := by fin_cases p <;> decide
  rw [positionParity, add_right_comm, h, zero_add]

private theorem signedTrig_product_add_nat (z : ℂ) (k : ℕ) :
    signedTrig 0 (z + (k : ℂ)) * signedTrig 1 (z + (k : ℂ)) =
      (-I) ^ (2 * k) * (signedTrig 0 z * signedTrig 1 z) := by
  simp only [signedTrig_add_nat, zero_add]
  rw [add_comm (1 : Fin 2), mul_mul_mul_comm, signedTrig_mul_toggle, ← pow_add, two_mul]

private theorem denC_reflection (z : ℂ) :
    denC (1 - z) * denC z = cos (Real.pi * z / 2) * sin (Real.pi * z / 2) := by
  rw [denC_eq, denC_eq, show 1 - z + 1 = 2 - z by ring,
    mul_comm (denR z), mul_mul_mul_comm, mul_comm (denR (2 - z)),
    denR_reflection_even, denR_reflection_odd]

private theorem inducedRatio_eq (k : ℕ) (z : ℂ)
    (h₁ : denC (z + (k : ℂ) / 2) ≠ 0) (h₂ : denC (z - (k : ℂ) / 2) ≠ 0) :
    inducedRatio k z =
      (-I) ^ k * (signedTrig 0 (z - (k : ℂ) / 2) * signedTrig 1 (z - (k : ℂ) / 2)) /
        (denC (z + (k : ℂ) / 2) * denC (z - (k : ℂ) / 2)) := by
  rw [inducedRatio, show 1 - z + (k : ℂ) / 2 = 1 - (z - (k : ℂ) / 2) by ring,
    signedTrig_zero, signedTrig_one, div_eq_div_iff h₁ (mul_ne_zero h₁ h₂), pow_succ]
  calc
    _ = (-I) ^ k * (-I) * (denC (1 - (z - (k : ℂ) / 2)) * denC (z - (k : ℂ) / 2)) *
          denC (z + (k : ℂ) / 2) := by ac_rfl
    _ = _ := by rw [denC_reflection]; ring

/-- The two real characters with opposite shifts and the induced block have the
same inverse Gamma ratio, provided their parities differ by `k + 1` modulo two. -/
theorem characterRatio_mul_eq_induced (k : ℕ) (p q : Fin 2)
    (hpq : p + Fin.ofNat 2 k = q + 1) (z : ℂ)
    (h₁ : denC (z + (k : ℂ) / 2) ≠ 0) (h₂ : denC (z - (k : ℂ) / 2) ≠ 0) :
    characterRatio p (z + (k : ℂ) / 2) * characterRatio q (z - (k : ℂ) / 2) =
      inducedRatio k z := by
  rw [characterRatio_eq _ _ h₁, characterRatio_eq _ _ h₂, inducedRatio_eq _ _ h₁ h₂,
    ← mul_div_mul_comm]
  congr 1
  rw [show z + (k : ℂ) / 2 = z - (k : ℂ) / 2 + (k : ℂ) by ring,
    signedTrig_add_nat, hpq]
  rw [mul_assoc, mul_comm (signedTrig (q + 1) _), signedTrig_mul_toggle]

/-- The four products of position characters of two induced blocks have the same
inverse Gamma ratio as the two induced tensor factors. The spectral variable
includes the sum of the two exponents. -/
theorem characterRatio_tensor (m n : ℕ) (hmn : n ≤ m) (z : ℂ)
    (hpp : denC (z + ((m : ℂ) + (n : ℂ)) / 2) ≠ 0)
    (hpm : denC (z + ((m : ℂ) - (n : ℂ)) / 2) ≠ 0)
    (hmp : denC (z - ((m : ℂ) - (n : ℂ)) / 2) ≠ 0)
    (hmm : denC (z - ((m : ℂ) + (n : ℂ)) / 2) ≠ 0) :
    characterRatio (positionParity m + positionParity n) (z + ((m : ℂ) + (n : ℂ)) / 2) *
        characterRatio (positionParity m) (z + ((m : ℂ) - (n : ℂ)) / 2) *
        characterRatio (positionParity n) (z - ((m : ℂ) - (n : ℂ)) / 2) *
        characterRatio 0 (z - ((m : ℂ) + (n : ℂ)) / 2) =
      inducedRatio (m + n) z * inducedRatio (m - n) z := by
  have hpm' : denC (z + ((m - n : ℕ) : ℂ) / 2) ≠ 0 := by
    rwa [Nat.cast_sub hmn]
  have hmp' : denC (z - ((m - n : ℕ) : ℂ) / 2) ≠ 0 := by
    rwa [Nat.cast_sub hmn]
  have hpp' : denC (z + ((m + n : ℕ) : ℂ) / 2) ≠ 0 := by
    rwa [Nat.cast_add]
  have hmm' : denC (z - ((m + n : ℕ) : ℂ) / 2) ≠ 0 := by
    rwa [Nat.cast_add]
  rw [characterRatio_eq _ _ hpp, characterRatio_eq _ _ hpm, characterRatio_eq _ _ hmp,
    characterRatio_eq _ _ hmm, inducedRatio_eq _ _ hpp' hmm', inducedRatio_eq _ _ hpm' hmp']
  simp only [Nat.cast_add, Nat.cast_sub hmn]
  let x := z - ((m : ℂ) + (n : ℂ)) / 2
  have hxpp : z + ((m : ℂ) + (n : ℂ)) / 2 = x + ((m + n : ℕ) : ℂ) := by
    dsimp [x]
    push_cast
    ring
  have hxpm : z + ((m : ℂ) - (n : ℂ)) / 2 = x + (m : ℂ) := by dsimp [x]; ring
  have hxmp : z - ((m : ℂ) - (n : ℂ)) / 2 = x + (n : ℂ) := by dsimp [x]; ring
  have hparity : positionParity m + positionParity n + Fin.ofNat 2 (m + n) = 0 := by
    rw [parity_add, add_add_add_comm, positionParity_add, positionParity_add]
    decide
  simp only [← mul_div_mul_comm]
  congr 1
  · conv_rhs => rw [hxmp, signedTrig_product_add_nat]
    rw [hxpp, hxpm, hxmp, signedTrig_add_nat, signedTrig_add_nat, signedTrig_add_nat,
      hparity, positionParity_add, positionParity_add]
    calc
      _ = (-I) ^ (m + n) * ((-I) ^ m * (-I) ^ n) *
          (signedTrig 0 x * signedTrig 1 x) ^ 2 := by
        change (-I) ^ (m + n) * signedTrig 0 x * ((-I) ^ m * signedTrig 1 x) *
          ((-I) ^ n * signedTrig 1 x) * signedTrig 0 x = _
        rw [pow_two]
        ac_rfl
      _ = (-I) ^ (m + n) * ((-I) ^ (m - n) * (-I) ^ (2 * n)) *
          (signedTrig 0 x * signedTrig 1 x) ^ 2 := by
        rw [← pow_add (-I) m n, ← pow_add (-I) (m - n) (2 * n),
          show m - n + 2 * n = m + n by omega]
      _ = _ := by
        rw [pow_two]
        ac_rfl
  · ac_rfl

end Langlands.LocalFactor.Archimedean.RealGammaReflection
