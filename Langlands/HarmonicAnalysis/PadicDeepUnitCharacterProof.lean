import Langlands.HarmonicAnalysis.PadicDeepUnitCharacterStatement
import Langlands.LocalField.Normalization.Proof

/-! Kill the exact multiplication error and then a uniform prime-power multiple. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe u

private theorem valuation_le_exp_neg_ord {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) (x : F.Carrier) :
    T.discreteValuation x ≤ WithZero.exp (-T.ord x) := by
  apply WithZero.le_exp_of_log_le
  simp only [PadicField.TopologicalData.ord, neg_neg, le_refl]

/-- The first-order formula is a continuous principal-unit character of p-power order. -/
theorem padicDeepUnitCharacter : PadicDeepUnitCharacterStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ c n hquad
  have herror (z w : T.principalUnits n) :
      ψ (c * (((z : F.Carrierˣ) : F.Carrier) - 1) *
        (((w : F.Carrierˣ) : F.Carrier) - 1)) = 1 := by
    apply (T.additiveConductor_spec ψ).1
    change T.discreteValuation _ ≤ _
    calc
      T.discreteValuation (c * (((z : F.Carrierˣ) : F.Carrier) - 1) *
          (((w : F.Carrierˣ) : F.Carrier) - 1)) =
          T.discreteValuation c *
            T.discreteValuation (((z : F.Carrierˣ) : F.Carrier) - 1) *
            T.discreteValuation (((w : F.Carrierˣ) : F.Carrier) - 1) := by
              simp only [map_mul]
      _ ≤ T.discreteValuation c * WithZero.exp (-(n : ℤ)) *
          WithZero.exp (-(n : ℤ)) :=
        mul_le_mul' (mul_le_mul' le_rfl z.property.2) w.property.2
      _ = T.discreteValuation c * WithZero.exp (-(2 * (n : ℤ))) := by
        rw [mul_assoc, ← WithZero.exp_add]
        congr 2
        ring
      _ ≤ _ := hquad
  let η : T.principalUnits n →ₜ* Circle :=
    { toFun z := ψ (c * (((z : F.Carrierˣ) : F.Carrier) - 1))
      map_one' := by simp
      map_mul' := by
        intro z w
        change ψ (c * (((z : F.Carrierˣ) : F.Carrier) *
          ((w : F.Carrierˣ) : F.Carrier) - 1)) = _
        rw [show c * (((z : F.Carrierˣ) : F.Carrier) *
            ((w : F.Carrierˣ) : F.Carrier) - 1) =
          (c * (((z : F.Carrierˣ) : F.Carrier) - 1) +
            c * (((w : F.Carrierˣ) : F.Carrier) - 1)) +
            c * (((z : F.Carrierˣ) : F.Carrier) - 1) *
              (((w : F.Carrierˣ) : F.Carrier) - 1) by ring]
        rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, herror, mul_one]
      continuous_toFun := ψ.continuous_toFun.comp
        (continuous_const.mul
          ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const)) }
  refine ⟨η, fun z => rfl, ?_⟩
  let k : ℕ := (-T.ord c - T.additiveConductor ψ).toNat
  have hk : -T.ord c - T.additiveConductor ψ ≤ (k : ℤ) := Int.self_le_toNat _
  have hpv : T.discreteValuation ((p : F.Carrier) ^ k) ≤ WithZero.exp (-(k : ℤ)) := by
    apply (valuation_le_exp_neg_ord T _).trans
    apply WithZero.exp_le_exp.mpr
    have hord : T.ord ((p : F.Carrier) ^ k) = (k : ℤ) * T.ord (p : F.Carrier) := by
      simpa using T.ord_zpow (p : F.Carrier) (k : ℤ)
    rw [hord]
    have he : 1 ≤ T.ord (p : F.Carrier) := T.ord_prime_pos
    nlinarith [Int.natCast_nonneg k]
  refine ⟨k, ContinuousMonoidHom.ext fun z => ?_⟩
  simp only [ContinuousMonoidHom.pow_apply]
  change ψ (c * (((z : F.Carrierˣ) : F.Carrier) - 1)) ^ (p ^ k) = 1
  rw [← AddChar.map_nsmul_eq_pow]
  apply (T.additiveConductor_spec ψ).1
  change T.discreteValuation _ ≤ _
  rw [nsmul_eq_mul, Nat.cast_pow]
  calc
    T.discreteValuation ((p : F.Carrier) ^ k *
        (c * (((z : F.Carrierˣ) : F.Carrier) - 1))) =
      T.discreteValuation ((p : F.Carrier) ^ k) *
        (T.discreteValuation c *
          T.discreteValuation (((z : F.Carrierˣ) : F.Carrier) - 1)) := by
            simp only [map_mul]
    _ ≤ WithZero.exp (-(k : ℤ)) *
        (WithZero.exp (-T.ord c) * WithZero.exp (-(n : ℤ))) :=
      mul_le_mul' hpv (mul_le_mul' (valuation_le_exp_neg_ord T c) z.property.2)
    _ = WithZero.exp (-(k : ℤ) - T.ord c - (n : ℤ)) := by
      rw [← WithZero.exp_add, ← WithZero.exp_add]
      congr 1
      ring
    _ ≤ WithZero.exp (T.additiveConductor ψ) := by
      apply WithZero.exp_le_exp.mpr
      omega

end Langlands.HarmonicAnalysis
