import Langlands.Representation.Twist.LeviRealPower
import Langlands.Representation.Shahidi.Induction

/-! # Complex determinant characters and twists on actual product Levis -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The product of the actual block determinant characters with complex exponents. -/
def leviComplexPowerCharacter (z : Fin B.length → ℂ) : B.Levi F.Carrier →* ℂˣ :=
  ∏ i, Shahidi.complexPower (T.blockDeterminantNorm B i) (z i)

@[simp]
theorem leviComplexPowerCharacter_apply (z : Fin B.length → ℂ) (m : B.Levi F.Carrier) :
    T.leviComplexPowerCharacter B z m =
      ∏ i, T.determinantComplexPower (B.size i) (z i) (m i) := by
  simp [leviComplexPowerCharacter, determinantComplexPower_eq_complexPower,
    Shahidi.complexPower, blockDeterminantNorm]

/-- The complex powers use the residue-normalized absolute values of actual determinants. -/
theorem coe_leviComplexPowerCharacter (z : Fin B.length → ℂ) (m : B.Levi F.Carrier) :
    (T.leviComplexPowerCharacter B z m : ℂ) =
      ∏ i, (T.normalizedAbs (GeneralLinear.determinant (m i) : F.Carrier) : ℂ) ^
        z i := by
  simp [leviComplexPowerCharacter, Shahidi.complexPower_apply]

@[simp]
theorem leviComplexPowerCharacter_zero :
    T.leviComplexPowerCharacter B 0 = 1 := by
  simp [leviComplexPowerCharacter]

theorem leviComplexPowerCharacter_add (z w : Fin B.length → ℂ) :
    T.leviComplexPowerCharacter B (z + w) =
      T.leviComplexPowerCharacter B z * T.leviComplexPowerCharacter B w := by
  simp only [leviComplexPowerCharacter, Pi.add_apply, Shahidi.complexPower_add,
    Finset.prod_mul_distrib]

theorem leviComplexPowerCharacter_neg (z : Fin B.length → ℂ) :
    T.leviComplexPowerCharacter B (-z) = (T.leviComplexPowerCharacter B z)⁻¹ := by
  apply MonoidHom.ext
  intro m
  simp [leviComplexPowerCharacter, Shahidi.complexPower_neg]

/-- Real complex exponents recover the published real determinant character. -/
@[simp]
theorem leviComplexPowerCharacter_ofReal (t : Fin B.length → ℝ) :
    T.leviComplexPowerCharacter B (fun i => (t i : ℂ)) =
      T.leviRealPowerCharacter B t := by
  simp only [leviComplexPowerCharacter, Shahidi.complexPower_ofReal, leviRealPowerCharacter]

/-- Every simultaneous determinant-norm-one element is in the character kernel. -/
theorem normOneLevi_le_ker_leviComplexPowerCharacter (z : Fin B.length → ℂ) :
    T.normOneLevi B ≤ (T.leviComplexPowerCharacter B z).ker := by
  intro m hm
  have h := (T.mem_normOneLevi B m).mp hm
  change T.leviComplexPowerCharacter B z m = 1
  apply Units.ext
  rw [T.coe_leviComplexPowerCharacter B]
  have hAbs (i : Fin B.length) :
      T.normalizedAbs (GeneralLinear.determinant (m i) : F.Carrier) = 1 := by
    change ((T.determinantNorm (B.size i) (m i) : ℝ≥0) : ℝ) = 1
    rw [h i]
    rfl
  simp only [hAbs, Complex.ofReal_one, Complex.one_cpow, Finset.prod_const_one,
    Units.val_one]

theorem isOpen_ker_leviComplexPowerCharacter (z : Fin B.length → ℂ) :
    let := T.topology
    IsOpen ((T.leviComplexPowerCharacter B z).ker : Set (B.Levi F.Carrier)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact Subgroup.isOpen_mono (T.normOneLevi_le_ker_leviComplexPowerCharacter B z)
    (T.isOpen_normOneLevi B)

/-- The norm depends exactly on the real parts of the determinant exponents. -/
theorem norm_leviComplexPowerCharacter (z : Fin B.length → ℂ) (m : B.Levi F.Carrier) :
    ‖(T.leviComplexPowerCharacter B z m : ℂ)‖ =
      ∏ i, T.normalizedAbs (GeneralLinear.determinant (m i) : F.Carrier) ^
        (z i).re := by
  rw [T.coe_leviComplexPowerCharacter B, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact Complex.norm_cpow_eq_rpow_re_of_pos
    (T.normalizedAbs_pos (GeneralLinear.determinant (m i)).ne_zero) (z i)

/-- Every real source parameter gives a unitary character after multiplication by `I`. -/
@[simp]
theorem norm_leviComplexPowerCharacter_imaginary (u : Fin B.length → ℝ)
    (m : B.Levi F.Carrier) :
    ‖(T.leviComplexPowerCharacter B (fun i => Complex.I * (u i : ℂ)) m : ℂ)‖ = 1 := by
  rw [T.norm_leviComplexPowerCharacter B]
  simp [Complex.mul_re]

/-- On block scalars the split-centre exponent is the block size times `z i`. -/
theorem coe_leviComplexPowerCharacter_blockScalar (z : Fin B.length → ℂ)
    (a : Fin B.length → F.Carrierˣ) :
    (T.leviComplexPowerCharacter B z (B.blockScalarLevi F.Carrier a) : ℂ) =
      ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((B.size i : ℂ) * z i) := by
  have h (i : Fin B.length) :
      (T.determinantComplexPower (B.size i) (z i) (GeneralLinear.scalar (a i)) : ℂ) =
        (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((B.size i : ℂ) * z i) := by
    rw [T.determinantComplexPower_apply, T.determinantNorm_scalar]
    simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow, normalizedAbsUnits_coe]
    rw [← Real.rpow_natCast, ← Complex.cpow_mul_ofReal_nonneg (T.normalizedAbs_nonneg _),
      Complex.ofReal_natCast]
  simpa using congrArg (fun f : Fin B.length → ℂ => ∏ i, f i) (funext h)

/-- Compatible realizations yield the same complex character. -/
theorem leviComplexPowerCharacter_eq_topologicalData (U : F.TopologicalData)
    (z : Fin B.length → ℂ) :
    T.leviComplexPowerCharacter B z = U.leviComplexPowerCharacter B z := by
  apply MonoidHom.ext
  intro m
  simp only [leviComplexPowerCharacter_apply, determinantComplexPower_eq_complexPower,
    T.determinantNorm_eq U]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Twist an arbitrary actual Levi representation on its existing complex carrier. -/
def leviComplexPowerTwist (z : Fin B.length → ℂ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation ℂ (B.Levi F.Carrier) V :=
  twist (T.leviComplexPowerCharacter B z) σ

@[simp]
theorem leviComplexPowerTwist_apply (z : Fin B.length → ℂ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) (m : B.Levi F.Carrier) (v : V) :
    T.leviComplexPowerTwist B z σ m v = (T.leviComplexPowerCharacter B z m : ℂ) • σ m v :=
  rfl

@[simp]
theorem leviComplexPowerTwist_zero (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviComplexPowerTwist B 0 σ = σ := by
  simp [leviComplexPowerTwist]

theorem leviComplexPowerTwist_add (z w : Fin B.length → ℂ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviComplexPowerTwist B (z + w) σ =
      T.leviComplexPowerTwist B z (T.leviComplexPowerTwist B w σ) := by
  simp only [leviComplexPowerTwist, leviComplexPowerCharacter_add, twist_twist]

@[simp]
theorem leviComplexPowerTwist_neg_cancel (z : Fin B.length → ℂ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviComplexPowerTwist B (-z) (T.leviComplexPowerTwist B z σ) = σ := by
  simp [leviComplexPowerTwist, leviComplexPowerCharacter_neg]

@[simp]
theorem leviComplexPowerTwist_cancel_neg (z : Fin B.length → ℂ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviComplexPowerTwist B z (T.leviComplexPowerTwist B (-z) σ) = σ := by
  simp [leviComplexPowerTwist, leviComplexPowerCharacter_neg]

@[simp]
theorem leviComplexPowerTwist_ofReal (t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviComplexPowerTwist B (fun i => (t i : ℂ)) σ = T.leviRealPowerTwist B t σ := by
  simp only [leviComplexPowerTwist, leviComplexPowerCharacter_ofReal, leviRealPowerTwist]

theorem isSmooth_leviComplexPowerTwist_iff (z : Fin B.length → ℂ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    let := T.topology
    IsSmooth (T.leviComplexPowerTwist B z σ) ↔ IsSmooth σ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact isSmooth_twist_iff _ σ (T.isOpen_ker_leviComplexPowerCharacter B z)

end Langlands.PadicField.TopologicalData
