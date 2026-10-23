import Langlands.Group.GL.BlockModulus
import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Twist.RealPower
import Langlands.Representation.Twist.AlgebraProof

/-! # Real determinant characters and twists on actual product Levis -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The product of the actual block determinant characters with real exponents. -/
def leviRealPowerCharacter (t : Fin B.length → ℝ) : B.Levi F.Carrier →* ℂˣ :=
  ∏ i, realPowerCharacter (T.blockDeterminantNorm B i) (t i)

@[simp]
theorem leviRealPowerCharacter_apply (t : Fin B.length → ℝ) (m : B.Levi F.Carrier) :
    T.leviRealPowerCharacter B t m =
      ∏ i, realPowerCharacter (T.determinantNorm (B.size i)) (t i) (m i) := by
  simp [leviRealPowerCharacter, realPowerCharacter, blockDeterminantNorm]

/-- The exponents use the residue-normalized absolute value of each determinant. -/
theorem coe_leviRealPowerCharacter (t : Fin B.length → ℝ) (m : B.Levi F.Carrier) :
    (T.leviRealPowerCharacter B t m : ℂ) =
      ∏ i, (T.normalizedAbs (GeneralLinear.determinant (m i) : F.Carrier) ^ t i : ℝ) := by
  simp

@[simp]
theorem leviRealPowerCharacter_zero :
    T.leviRealPowerCharacter B 0 = 1 := by
  simp [leviRealPowerCharacter]

theorem leviRealPowerCharacter_add (s t : Fin B.length → ℝ) :
    T.leviRealPowerCharacter B (s + t) =
      T.leviRealPowerCharacter B s * T.leviRealPowerCharacter B t := by
  simp only [leviRealPowerCharacter, Pi.add_apply, realPowerCharacter_add, Finset.prod_mul_distrib]

theorem leviRealPowerCharacter_neg (t : Fin B.length → ℝ) :
    T.leviRealPowerCharacter B (-t) = (T.leviRealPowerCharacter B t)⁻¹ := by
  apply MonoidHom.ext
  intro m
  simp [leviRealPowerCharacter, realPowerCharacter_neg]

/-- Every simultaneous determinant-norm-one element is in the character kernel. -/
theorem normOneLevi_le_ker_leviRealPowerCharacter (t : Fin B.length → ℝ) :
    T.normOneLevi B ≤ (T.leviRealPowerCharacter B t).ker := by
  intro m hm
  have h := (T.mem_normOneLevi B m).mp hm
  change T.leviRealPowerCharacter B t m = 1
  simp [realPowerCharacter, h]

theorem isOpen_ker_leviRealPowerCharacter (t : Fin B.length → ℝ) :
    let := T.topology
    IsOpen ((T.leviRealPowerCharacter B t).ker : Set (B.Levi F.Carrier)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact Subgroup.isOpen_mono (T.normOneLevi_le_ker_leviRealPowerCharacter B t)
    (T.isOpen_normOneLevi B)

/-- On block scalars the split-centre exponent is the block size times `t i`. -/
theorem coe_leviRealPowerCharacter_blockScalar (t : Fin B.length → ℝ)
    (a : Fin B.length → F.Carrierˣ) :
    (T.leviRealPowerCharacter B t (B.blockScalarLevi F.Carrier a) : ℂ) =
      ∏ i, (T.normalizedAbs (a i : F.Carrier) ^ ((B.size i : ℝ) * t i) : ℝ) := by
  have h (i : Fin B.length) :
      (realPowerCharacter (T.determinantNorm (B.size i)) (t i)
        (GeneralLinear.scalar (a i)) : ℂ) =
        (T.normalizedAbs (a i : F.Carrier) ^ ((B.size i : ℝ) * t i) : ℝ) := by
    simp only [coe_realPowerCharacter, determinantNorm_scalar,
      Units.val_pow_eq_pow_val, NNReal.coe_pow, normalizedAbsUnits_coe]
    rw [Real.rpow_natCast_mul (T.normalizedAbs_nonneg _) (B.size i) (t i)]
  simpa using congrArg (fun f : Fin B.length → ℂ => ∏ i, f i) (funext h)

/-- Restriction to the ambient scalar centre adds the weighted exponents. -/
theorem coe_leviRealPowerCharacter_scalar (t : Fin B.length → ℝ) (a : F.Carrierˣ) :
    (T.leviRealPowerCharacter B t (fun i => GeneralLinear.scalar (n := B.size i) a) : ℂ) =
      (T.normalizedAbs (a : F.Carrier) ^ (∑ i, (B.size i : ℝ) * t i) : ℝ) := by
  change (T.leviRealPowerCharacter B t (B.blockScalarLevi F.Carrier (fun _ => a)) : ℂ) = _
  rw [T.coe_leviRealPowerCharacter_blockScalar B]
  rw [Real.rpow_sum_of_pos (T.normalizedAbs_pos a.ne_zero)]

/-- Compatible realizations yield the same character. -/
theorem leviRealPowerCharacter_eq_topologicalData (U : F.TopologicalData)
    (t : Fin B.length → ℝ) :
    T.leviRealPowerCharacter B t = U.leviRealPowerCharacter B t := by
  apply MonoidHom.ext
  intro m
  simp only [leviRealPowerCharacter_apply, T.determinantNorm_eq U]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Twist an arbitrary actual Levi representation, without choosing tensor factors. -/
def leviRealPowerTwist (t : Fin B.length → ℝ) (σ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation ℂ (B.Levi F.Carrier) V :=
  twist (T.leviRealPowerCharacter B t) σ

@[simp]
theorem leviRealPowerTwist_apply (t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) (m : B.Levi F.Carrier) (v : V) :
    T.leviRealPowerTwist B t σ m v = (T.leviRealPowerCharacter B t m : ℂ) • σ m v := rfl

@[simp]
theorem leviRealPowerTwist_zero (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviRealPowerTwist B 0 σ = σ := by
  simp [leviRealPowerTwist]

theorem leviRealPowerTwist_add (s t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviRealPowerTwist B (s + t) σ =
      T.leviRealPowerTwist B s (T.leviRealPowerTwist B t σ) := by
  simp only [leviRealPowerTwist, leviRealPowerCharacter_add, twist_twist]

@[simp]
theorem leviRealPowerTwist_neg_cancel (t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviRealPowerTwist B (-t) (T.leviRealPowerTwist B t σ) = σ := by
  simp [leviRealPowerTwist, leviRealPowerCharacter_neg]

@[simp]
theorem leviRealPowerTwist_cancel_neg (t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    T.leviRealPowerTwist B t (T.leviRealPowerTwist B (-t) σ) = σ := by
  simp [leviRealPowerTwist, leviRealPowerCharacter_neg]

theorem isSmooth_leviRealPowerTwist_iff (t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    let := T.topology
    IsSmooth (T.leviRealPowerTwist B t σ) ↔ IsSmooth σ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact isSmooth_twist_iff _ σ (T.isOpen_ker_leviRealPowerCharacter B t)

end Langlands.PadicField.TopologicalData
