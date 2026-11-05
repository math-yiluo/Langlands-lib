import Langlands.Global.Arithmetic.AuxiliaryFirstOrderTopology

/-! Actual norm bounds, nonzero trace coordinates and norm-one deep-unit witnesses. -/

noncomputable section

namespace Langlands.Global.AuxiliaryFirstOrder

universe u v

/-- A discrete valuation bound gives the same bound for the actual base-extending norm. -/
theorem canonicalNorm_le_of_valuation_le {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) (a b : F.Carrier)
    (hb : b ≠ 0) (h : T.discreteValuation a ≤ T.discreteValuation b) :
    F.canonicalNorm a ≤ F.canonicalNorm b := by
  have hbv : 0 < T.discreteValuation b :=
    pos_iff_ne_zero.mpr (T.discreteValuation.ne_zero_iff.mpr hb)
  have hq : a / b ∈ T.Integers :=
    (T.mem_integers_iff_discreteValuation_le_one _).mpr (by
      rw [T.discreteValuation.map_div]
      exact (div_le_one₀ hbv).mpr h)
  have hn := (T.canonicalNorm_le_one_iff_mem_integers _).mpr hq
  let := F.canonicalNormedField
  change ‖a / b‖ ≤ 1 at hn
  change ‖a‖ ≤ ‖b‖
  rw [norm_div] at hn
  exact (div_le_one₀ (norm_pos_iff.mpr hb)).mp hn

/-- Prime powers have exactly their usual base p-adic norm in every finite extension. -/
theorem canonicalNorm_prime_pow {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (k : ℕ) :
    F.canonicalNorm ((p : F.Carrier) ^ k) = (p : ℝ) ^ (-(k : ℤ)) := by
  have h := F.canonicalNorm_algebraMap ((p : Padic p) ^ k)
  simpa only [map_pow, map_natCast, Padic.norm_p_pow] using h

/-- The weighted trace is a nonzero actual base-linear functional. -/
theorem weighted_trace_ne_zero {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] [Algebra.IsSeparable F M]
    (L : IntermediateField F M) (b : L) (hb : b ≠ 0) :
    (Algebra.trace F M).comp (LinearMap.mul F M (b : M)) ≠ 0 := by
  intro h
  apply Algebra.trace_ne_zero F M
  have hbM : (b : M) ≠ 0 := fun hh => hb (Subtype.ext hh)
  ext x
  have hx := congrArg (fun δ : M →ₗ[F] F => δ ((b : M)⁻¹ * x)) h
  change Algebra.trace F M ((b : M) * ((b : M)⁻¹ * x)) = 0 at hx
  rw [← mul_assoc, mul_inv_cancel₀ hbM, one_mul] at hx
  exact hx

/-- Every actual integral coordinate gives a norm-one unit at each positive prime-power level. -/
theorem exists_norm_one_coordinate_unit {p : ℕ} [Fact p.Prime]
    (M : PadicField.{v} p) :
    letI := M.canonicalNormedField
    ∀ (k : ℕ), 0 < k → ∀ y : M.canonicalTopologicalData.Integers,
      ∃ z : M.Carrierˣ,
        (z : M.Carrier) = 1 + (p : M.Carrier) ^ k * (y : M.Carrier) ∧
        ‖(z : M.Carrier)‖ = 1 := by
  let := M.canonicalNormedField
  intro k hk y
  have hnp : ‖(p : M.Carrier)‖ < 1 := by
    have he := M.canonicalNorm_algebraMap (p : Padic p)
    rw [map_natCast] at he
    exact he.trans_lt Padic.norm_p_lt_one
  have hpow : ‖(p : M.Carrier) ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hnp (Nat.ne_of_gt hk)
  have hy : ‖(y : M.Carrier)‖ ≤ 1 :=
    (M.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers _).mpr y.property
  have hsmall : ‖(p : M.Carrier) ^ k * (y : M.Carrier)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_lt (by simpa using hpow)
  have hna : IsNonarchimedean (norm : M.Carrier → ℝ) :=
    isNonarchimedean_spectralNorm (K := Padic p) (L := M.Carrier)
  have hnorm : ‖1 + (p : M.Carrier) ^ k * (y : M.Carrier)‖ = 1 := by
    simpa only [norm_one] using hna.add_eq_left_of_lt
      (a := (p : M.Carrier) ^ k * (y : M.Carrier)) (b := (1 : M.Carrier))
      norm_neg (by simpa only [norm_one] using hsmall)
  have hz : 1 + (p : M.Carrier) ^ k * (y : M.Carrier) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  exact ⟨Units.mk0 _ hz, rfl, hnorm⟩

end Langlands.Global.AuxiliaryFirstOrder
