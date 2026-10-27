import Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityStatement
import Langlands.LocalField.Normalization.Proof
import Langlands.ClassField.Global.LocalPowerIndex

/-! # Principal-unit powers and uniform conductor bounds -/

noncomputable section

open scoped WithZero
open IsLocalRing

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The actual valuation integer ring is complete for its maximal-ideal-adic topology.
This is Mathlib's local-field instance, applied to the topology recorded in `T`. -/
theorem isAdicComplete_integers :
    IsAdicComplete (maximalIdeal T.Integers) T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  have := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  exact inferInstance

/-- Every fixed positive power of `Uᵇ` contains a deeper principal-unit subgroup. -/
theorem exists_principalUnits_subset_pow (b m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, ∀ u : F.Carrierˣ, u ∈ T.principalUnits N →
      ∃ v : F.Carrierˣ, v ∈ T.principalUnits b ∧ v ^ m = u := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.isAdicComplete_integers
  have : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have hm0 : (m : F.Carrier) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmv : T.discreteValuation (m : F.Carrier) ≠ 0 :=
    T.discreteValuation.ne_zero_iff.mpr hm0
  obtain ⟨j, hj⟩ : ∃ j : ℤ, T.discreteValuation (m : F.Carrier) = WithZero.exp j :=
    ⟨_, (WithZero.exp_log hmv).symm⟩
  have hj0 : j ≤ 0 := by
    have h1 : T.discreteValuation (m : F.Carrier) ≤ 1 :=
      (T.mem_integers_iff_discreteValuation_le_one _).mp (natCast_mem T.Integers m)
    rwa [hj, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  refine ⟨2 * (-j).toNat + (b + 1), fun u hu => ?_⟩
  have hπ0 : T.uniformizer ≠ 0 := by
    intro h
    have := T.discreteValuation_uniformizer
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hπk : T.discreteValuation (T.uniformizer ^ (b + 1)) =
      WithZero.exp (-((b + 1 : ℕ) : ℤ)) := by
    rw [map_pow, T.discreteValuation_uniformizer, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hcmem : T.uniformizer ^ (b + 1) ∈ T.Integers := by
    rw [T.mem_integers_iff_discreteValuation_le_one, hπk, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    omega
  let c : T.Integers := ⟨T.uniformizer ^ (b + 1), hcmem⟩
  have hc : c ∈ maximalIdeal T.Integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
    apply e.strictMono.lt_iff_lt.mp
    change T.discreteValuation (T.uniformizer ^ (b + 1)) < e 1
    rw [map_one, hπk, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  let D : F.Carrier := (m : F.Carrier) ^ 2 * T.uniformizer ^ (b + 1)
  have hD0 : D ≠ 0 := mul_ne_zero (pow_ne_zero _ hm0) (pow_ne_zero _ hπ0)
  have hDv : T.discreteValuation D = WithZero.exp (2 * j - ((b + 1 : ℕ) : ℤ)) := by
    simp only [D, map_mul, map_pow, hj, hπk]
    rw [← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul, Nat.cast_ofNat,
      ← sub_eq_add_neg]
  have htmem : ((u : F.Carrier) - 1) / D ∈ T.Integers := by
    rw [T.mem_integers_iff_discreteValuation_le_one, map_div₀, hDv,
      div_le_one₀ (WithZero.exp_pos)]
    refine hu.2.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  let t : T.Integers := ⟨_, htmem⟩
  obtain ⟨z, hz⟩ := Langlands.ClassField.Global.exists_one_add_mul_mul_pow_eq
    (maximalIdeal T.Integers) m hm.ne' c hc t
  have hz' : (1 + (m : F.Carrier) * T.uniformizer ^ (b + 1) * z) ^ m = u := by
    have h := congrArg Subtype.val hz
    push_cast at h
    rw [h]
    change 1 + (m : F.Carrier) ^ 2 * T.uniformizer ^ (b + 1) * (((u : F.Carrier) - 1) / D) = u
    rw [show (m : F.Carrier) ^ 2 * T.uniformizer ^ (b + 1) = D from rfl, mul_div_cancel₀ _ hD0]
    ring
  have hz1 : T.discreteValuation (z : F.Carrier) ≤ 1 :=
    (T.mem_integers_iff_discreteValuation_le_one _).mp z.2
  have hwv : T.discreteValuation ((m : F.Carrier) * T.uniformizer ^ (b + 1) * z) ≤
      WithZero.exp (-((b + 1 : ℕ) : ℤ)) := by
    rw [map_mul, map_mul, hπk]
    have hm1 : T.discreteValuation (m : F.Carrier) ≤ 1 := by
      rw [hj, ← WithZero.exp_zero, WithZero.exp_le_exp]
      exact hj0
    calc T.discreteValuation (m : F.Carrier) * WithZero.exp (-((b + 1 : ℕ) : ℤ)) *
          T.discreteValuation (z : F.Carrier)
        ≤ 1 * WithZero.exp (-((b + 1 : ℕ) : ℤ)) * 1 := by gcongr
      _ = WithZero.exp (-((b + 1 : ℕ) : ℤ)) := by simp
  have hwlt : T.discreteValuation ((m : F.Carrier) * T.uniformizer ^ (b + 1) * z) < 1 := by
    refine hwv.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hw1 : T.discreteValuation (1 + (m : F.Carrier) * T.uniformizer ^ (b + 1) * z) = 1 := by
    simpa using T.discreteValuation.map_add_eq_of_lt_left
      (x := 1) (y := (m : F.Carrier) * T.uniformizer ^ (b + 1) * z) (by simpa using hwlt)
  have hw0 : (1 + (m : F.Carrier) * T.uniformizer ^ (b + 1) * z) ≠ 0 := by
    intro h
    rw [h, map_zero] at hw1
    exact zero_ne_one hw1
  refine ⟨Units.mk0 _ hw0, ⟨hw1, ?_⟩, Units.ext ?_⟩
  · simp only [Units.val_mk0, add_sub_cancel_left]
    refine hwv.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · simp only [Units.val_pow_eq_pow_val, Units.val_mk0, hz']

/-- Large conductor forces a fixed positive character power to be nontrivial on `Uᵇ`.
The threshold is chosen before the character. -/
theorem exists_conductor_bound_pow_ne_one (b m : ℕ) (hm : 0 < m) :
    letI := T.topology
    ∃ A : ℕ, ∀ χ : HarmonicAnalysis.Quasicharacter F.Carrier,
      A ≤ T.multiplicativeConductor χ →
      ∃ v : F.Carrierˣ, v ∈ T.principalUnits b ∧ (χ v) ^ m ≠ 1 := by
  let := T.topology
  obtain ⟨N, hN⟩ := T.exists_principalUnits_subset_pow b m hm
  refine ⟨N + 1, fun χ hχ => ?_⟩
  obtain ⟨u, hu, hχu⟩ :=
    T.exists_nontrivial_below_multiplicativeConductor χ N (by omega)
  obtain ⟨v, hv, rfl⟩ := hN u hu
  exact ⟨v, hv, by rwa [map_pow] at hχu⟩

end Langlands.PadicField.TopologicalData

namespace Langlands.HarmonicAnalysis

universe uF

/-- Canonical principal-unit power cofinality and the uniform character-power bound. -/
theorem principalUnitPowerCofinality : PrincipalUnitPowerCofinalityStatement.{uF} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro b m hm
  exact ⟨T.exists_principalUnits_subset_pow b m hm,
    T.exists_conductor_bound_pow_ne_one b m hm⟩

end Langlands.HarmonicAnalysis
