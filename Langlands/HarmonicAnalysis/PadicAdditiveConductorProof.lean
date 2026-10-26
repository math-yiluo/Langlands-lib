import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalFactor.Harmonic.Statement

/-! Additive-conductor scaling and the actual integer-ring annihilator. -/

noncomputable section

open scoped WithZero

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

private theorem conductor_uniformizer_ne_zero : T.uniformizer ≠ 0 := by
  apply T.discreteValuation.ne_zero_iff.mp
  rw [T.discreteValuation_uniformizer]
  exact WithZero.exp_ne_zero

/-- Membership in the valuation lattice is membership in the actual fractional ideal. -/
theorem mem_additiveLattice_iff_exists_integer (n : ℤ) (x : F.Carrier) :
    x ∈ T.additiveLattice n ↔
      ∃ t : T.Integers, x = T.uniformizer ^ (-n) * (t : F.Carrier) := by
  rw [T.mem_additiveLattice_iff_div_mem_integers]
  have hπ := zpow_ne_zero (-n) T.conductor_uniformizer_ne_zero
  constructor
  · intro hx
    refine ⟨⟨x / T.uniformizer ^ (-n), hx⟩, ?_⟩
    dsimp
    field_simp
  · rintro ⟨t, rfl⟩
    rw [mul_div_cancel_left₀ _ hπ]
    exact t.property

private theorem discreteValuation_eq_exp_neg_ord {a : F.Carrier} (ha : a ≠ 0) :
    T.discreteValuation a = WithZero.exp (-T.ord a) := by
  simp only [ord, neg_neg]
  exact (WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr ha)).symm

/-- Multiplication transports the actual valuation lattices with the normalized order. -/
theorem mul_mem_additiveLattice_iff {a : F.Carrier} (ha : a ≠ 0)
    (n : ℤ) (x : F.Carrier) :
    a * x ∈ T.additiveLattice n ↔ x ∈ T.additiveLattice (n + T.ord a) := by
  rw [mem_additiveLattice, mem_additiveLattice, map_mul,
    T.discreteValuation_eq_exp_neg_ord ha, ← le_div_iff₀' WithZero.exp_pos,
    ← WithZero.exp_sub]
  simp only [sub_neg_eq_add]

/-- A raw character is trivial on the displayed fractional ideal exactly when
it is trivial on the corresponding valuation lattice. -/
theorem forall_integers_uniformizer_mul_iff (ψ : AddChar F.Carrier Circle) (n : ℤ) :
    (∀ t : T.Integers, ψ (T.uniformizer ^ (-n) * (t : F.Carrier)) = 1) ↔
      ∀ x ∈ T.additiveLattice n, ψ x = 1 := by
  constructor
  · intro h x hx
    obtain ⟨t, rfl⟩ := (T.mem_additiveLattice_iff_exists_integer n x).mp hx
    exact h t
  · intro h t
    exact h _ ((T.mem_additiveLattice_iff_exists_integer n _).mpr ⟨t, rfl⟩)

/-- The triviality index changes by `ord(a)` when the character is scaled. -/
theorem triviality_mulShift_iff (ψ : AddChar F.Carrier Circle) (a : F.Carrierˣ)
    (n : ℤ) :
    (∀ t : T.Integers,
      ψ.mulShift (a : F.Carrier) (T.uniformizer ^ (-n) * (t : F.Carrier)) = 1) ↔
    ∀ t : T.Integers,
      ψ (T.uniformizer ^ (-(n - T.ord (a : F.Carrier))) * (t : F.Carrier)) = 1 := by
  rw [T.forall_integers_uniformizer_mul_iff, T.forall_integers_uniformizer_mul_iff]
  simp only [AddChar.mulShift_apply]
  constructor
  · intro h x hx
    have hx' : (a⁻¹ : F.Carrierˣ) * x ∈ T.additiveLattice n := by
      apply (T.mul_mem_additiveLattice_iff a⁻¹.ne_zero n x).mpr
      simpa only [Units.val_inv_eq_inv_val, T.ord_inv, ← sub_eq_add_neg] using hx
    simpa only [Units.val_inv_eq_inv_val, ← mul_assoc, mul_inv_cancel₀ a.ne_zero,
      one_mul] using h _ hx'
  · intro h x hx
    apply h
    apply (T.mul_mem_additiveLattice_iff a.ne_zero _ x).mpr
    simpa only [sub_add_cancel] using hx

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- The existing conductor is the greatest triviality index in fractional-ideal form. -/
theorem isGreatest_fractionalIdeal_triviality (ψ : AdditiveCharacter) :
    IsGreatest {m : ℤ | ∀ t : T.Integers,
      ψ (T.uniformizer ^ (-m) * (t : F.Carrier)) = 1} (T.additiveConductor ψ) := by
  let := T.topology
  constructor
  · exact (T.forall_integers_uniformizer_mul_iff ψ.toAddChar _).mpr
      (T.additiveConductor_spec ψ).1
  · intro m hm
    exact (T.additiveConductor_spec ψ).2 m
      ((T.forall_integers_uniformizer_mul_iff ψ.toAddChar m).mp hm)

/-- The annihilator of the actual integer ring is the conductor lattice. -/
theorem integer_annihilator_iff_mem_additiveLattice (ψ : AdditiveCharacter)
    (y : F.Carrier) :
    (∀ t : T.Integers, ψ ((t : F.Carrier) * y) = 1) ↔
      y ∈ T.additiveLattice (T.additiveConductor ψ) := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst y
      exact (T.additiveLattice _).zero_mem
    have htriv : T.AdditiveTrivialAt ψ (-T.ord y) := by
      intro x hx
      have hxO : y⁻¹ * x ∈ T.Integers := by
        apply (T.mem_additiveLattice_zero _).mp
        apply (T.mul_mem_additiveLattice_iff (inv_ne_zero hy) 0 x).mpr
        simpa only [T.ord_inv, zero_add] using hx
      have hh := h ⟨y⁻¹ * x, hxO⟩
      simpa only [mul_right_comm y⁻¹ x y, inv_mul_cancel₀ hy, one_mul] using hh
    have hle := (T.additiveConductor_spec ψ).2 _ htriv
    rw [mem_additiveLattice, T.discreteValuation_eq_exp_neg_ord hy]
    exact WithZero.exp_le_exp.mpr hle
  · intro hy t
    apply (T.additiveConductor_spec ψ).1
    rw [mem_additiveLattice, map_mul]
    calc
      T.discreteValuation (t : F.Carrier) * T.discreteValuation y ≤
          1 * T.discreteValuation y :=
        mul_le_mul_of_nonneg_right
          ((T.mem_integers_iff_discreteValuation_le_one _).mp t.property) zero_le
      _ ≤ WithZero.exp (T.additiveConductor ψ) := by simpa using hy

end Langlands.PadicField.TopologicalData

namespace Langlands.HarmonicAnalysis

universe u

/-- The full published p-adic additive-conductor proposition, for every supplied topology. -/
theorem padicAdditiveConductor : LocalFactors.PadicAdditiveConductorStatement.{u} := by
  intro p hp F T
  let := T.topology
  intro ψ hψ hne
  let χ : UnitaryAdditiveCharacter F.Carrier := ⟨ψ, hψ, hne⟩
  have hc := T.isGreatest_fractionalIdeal_triviality χ
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨T.additiveConductor χ, hc, fun _ hn => hn.unique hc⟩
  · intro n hn a
    constructor
    · apply (T.triviality_mulShift_iff ψ a _).mpr
      simpa only [Set.mem_ofPred_eq, add_sub_cancel_right] using hn.1
    · intro m hm
      have hm' := hn.2 ((T.triviality_mulShift_iff ψ a m).mp hm)
      change m - T.ord (a : F.Carrier) ≤ n at hm'
      omega
  · intro n hn y
    have hn' : n = T.additiveConductor χ := hn.unique hc
    subst n
    exact (T.integer_annihilator_iff_mem_additiveLattice χ y).trans
      (T.mem_additiveLattice_iff_exists_integer _ y)

end Langlands.HarmonicAnalysis
