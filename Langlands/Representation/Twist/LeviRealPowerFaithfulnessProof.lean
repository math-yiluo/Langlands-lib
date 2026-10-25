import Langlands.Representation.Twist.LeviRealPowerFaithfulnessStatement

/-! Uniformizer evaluation separates every real determinant exponent. -/
noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- A uniformizer in one scalar block measures its size-weighted exponent. -/
theorem coe_leviRealPowerCharacter_uniformizer (t : Fin B.length → ℝ)
    (i : Fin B.length) :
    (T.leviRealPowerCharacter B t
      (B.blockScalarLevi F.Carrier
        (Pi.mulSingle i (LocalFactor.PadicAbelian.uniformizerUnit T))) : ℂ) =
      (((T.residueCardinality : ℝ) ^ (-(B.size i : ℝ) * t i) : ℝ) : ℂ) := by
  rw [T.coe_leviRealPowerCharacter_blockScalar B]
  have hq : 0 ≤ (T.residueCardinality : ℝ) := by positivity
  have hu : T.normalizedAbs (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) =
      (T.residueCardinality : ℝ)⁻¹ := by
    simpa using LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T 1
  rw [Finset.prod_eq_single i]
  · simp only [Pi.mulSingle_eq_same, hu]
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hq]
    congr 2
    ring
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji, T.normalizedAbs_one]
  · simp

/-- Restriction to block scalars is already faithful on the full real vector. -/
theorem leviRealPowerCharacter_blockScalar_injective :
    Function.Injective (fun t : Fin B.length → ℝ =>
      (T.leviRealPowerCharacter B t).comp (B.blockScalarLevi F.Carrier)) := by
  intro t u h
  funext i
  have he := congrArg
    (fun χ : (Fin B.length → F.Carrierˣ) →* ℂˣ =>
      (χ (Pi.mulSingle i (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℂ)) h
  simp only [MonoidHom.comp_apply, T.coe_leviRealPowerCharacter_uniformizer B] at he
  have hq : 1 < (T.residueCardinality : ℝ) := by
    exact_mod_cast T.residueCardinality_gt_one
  have hp := (Real.rpow_right_inj (lt_trans zero_lt_one hq) (ne_of_gt hq)).mp
    (Complex.ofReal_injective he)
  have hb : (B.size i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (B.positive i))
  exact mul_left_cancel₀ (neg_ne_zero.mpr hb) hp

/-- Real determinant characters on the actual product Levi determine all exponents. -/
theorem leviRealPowerCharacter_injective :
    Function.Injective (T.leviRealPowerCharacter B) := by
  intro t u h
  apply T.leviRealPowerCharacter_blockScalar_injective B
  exact congrArg (fun χ : B.Levi F.Carrier →* ℂˣ =>
    χ.comp (B.blockScalarLevi F.Carrier)) h

theorem leviRealPowerCharacter_blockScalar_eq_iff (t u : Fin B.length → ℝ) :
    (T.leviRealPowerCharacter B t).comp (B.blockScalarLevi F.Carrier) =
      (T.leviRealPowerCharacter B u).comp (B.blockScalarLevi F.Carrier) ↔ t = u :=
  (T.leviRealPowerCharacter_blockScalar_injective B).eq_iff

theorem leviRealPowerCharacter_eq_iff (t u : Fin B.length → ℝ) :
    T.leviRealPowerCharacter B t = T.leviRealPowerCharacter B u ↔ t = u :=
  (T.leviRealPowerCharacter_injective B).eq_iff

end Langlands.PadicField.TopologicalData

namespace Langlands

universe uF

/-- Exact faithfulness statement, including uniformizer evaluation and rank zero. -/
theorem leviRealPowerFaithfulness : LeviRealPowerFaithfulnessStatement.{uF} := by
  intro p _ F T n B
  exact ⟨T.coe_leviRealPowerCharacter_uniformizer B,
    T.leviRealPowerCharacter_blockScalar_injective B,
    T.leviRealPowerCharacter_injective B⟩

end Langlands
