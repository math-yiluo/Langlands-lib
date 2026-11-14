import Langlands.GroupScheme.Examples.SU3RootScaling

/-! # Scaling commutators in quadratic unitary root coordinates -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root.Parameters

universe u

section Ring

variable {A : Type u} [CommRing A] {c : RingInvolution A}

/-- The central correction to scaling a root parameter by `a - 1`. -/
def scalingCommutatorCentral (a : A) (p : Parameters c) : central c :=
  ⟨⟨(0, c.bar (a - 1) * p.second - (a - 1) * c.bar p.second), by
    simp only [map_sub, map_mul, map_one, RingInvolution.bar_bar, map_zero, zero_mul]
    ring⟩, rfl⟩

@[simp] theorem first_scalingCommutatorCentral (a : A) (p : Parameters c) :
    (scalingCommutatorCentral a p).val.first = 0 := rfl

@[simp] theorem second_scalingCommutatorCentral (a : A) (p : Parameters c) :
    (scalingCommutatorCentral a p).val.second =
      c.bar (a - 1) * p.second - (a - 1) * c.bar p.second := rfl

/-- The SU3 scaling commutator is a root factor times a literal central factor. -/
theorem scale_mul_inv_factorization (a : A) (p : Parameters c) :
    scale a p * p⁻¹ =
      scale (a - 1) p * (scalingCommutatorCentral a p).val := by
  apply ext
  · simp only [first_mul, first_scale, first_inv, first_scalingCommutatorCentral]
    ring
  · simp only [second_mul, second_scale, second_inv, first_scale, first_inv,
      first_scalingCommutatorCentral, second_scalingCommutatorCentral,
      map_neg, map_sub, map_one, map_zero, mul_zero, add_zero]
    linear_combination a * p.equation

end Ring

section Valuation

variable {L : Type u} [Field L] {c : RingInvolution L}
    (omega : AddValuation L (WithTop ℝ))
    (hinv : ∀ z : L, omega (c.bar z) = omega z)

include hinv in
/-- The central correction gains the scalar depth plus twice the root depth. -/
theorem scalingCommutatorCentral_mem (a : L) (p : Parameters c) (r s : ℝ)
    (ha : (r : WithTop ℝ) ≤ omega (a - 1))
    (hp : p ∈ filtration omega hinv s) :
    (scalingCommutatorCentral a p).val ∈ centralFiltration omega hinv (r + 2 * s) := by
  refine ⟨rfl, ?_⟩
  rw [second_scalingCommutatorCentral]
  apply omega.map_le_sub
  · rw [omega.map_mul, hinv, WithTop.coe_add]
    exact add_le_add ha hp
  · rw [omega.map_mul, hinv, WithTop.coe_add]
    exact add_le_add ha hp

include hinv in
/-- The first factor gains the full scalar depth, including at the identity. -/
theorem scale_sub_one_mem_filtration (a : L) (p : Parameters c) (r s : ℝ)
    (ha : (r : WithTop ℝ) ≤ omega (a - 1))
    (hp : p ∈ filtration omega hinv s) :
    scale (a - 1) p ∈ filtration omega hinv (r + s) := by
  rw [mem_filtration_iff_depth, depthA_scale omega hinv, WithTop.coe_add]
  exact add_le_add ha ((mem_filtration_iff_depth omega hinv s p).mp hp)

include hinv in
/-- A scaling commutator lies in a product of root and central filtrations. -/
theorem scale_mul_inv_mem_filtration_product (a : L) (p : Parameters c) (r s : ℝ)
    (ha : (r : WithTop ℝ) ≤ omega (a - 1))
    (hp : p ∈ filtration omega hinv s) :
    ∃ q ∈ filtration omega hinv (r + s),
      ∃ z ∈ centralFiltration omega hinv (r + 2 * s),
        scale a p * p⁻¹ = q * z :=
  ⟨scale (a - 1) p, scale_sub_one_mem_filtration omega hinv a p r s ha hp,
    (scalingCommutatorCentral a p).val,
    scalingCommutatorCentral_mem omega hinv a p r s ha hp,
    scale_mul_inv_factorization a p⟩

include hinv in
/-- The norm character is congruent to one at the same scalar depth. -/
theorem norm_sub_one_ge (a : L) (r : ℝ)
    (ha : (0 : WithTop ℝ) ≤ omega a)
    (hdelta : (r : WithTop ℝ) ≤ omega (a - 1)) :
    (r : WithTop ℝ) ≤ omega (a * c.bar a - 1) := by
  have heq : a * c.bar a - 1 = (a - 1) * c.bar a + c.bar (a - 1) := by
    rw [map_sub, map_one]
    ring
  rw [heq]
  apply omega.map_le_add
  · rw [omega.map_mul, hinv]
    exact (add_zero (r : WithTop ℝ)) ▸ add_le_add hdelta ha
  · rwa [hinv]

include hinv in
/-- On the literal double root, the entire commutator gains the full scalar depth. -/
theorem scale_mul_inv_mem_centralFiltration (a : L) (p : Parameters c) (r s : ℝ)
    (ha : (0 : WithTop ℝ) ≤ omega a)
    (hdelta : (r : WithTop ℝ) ≤ omega (a - 1))
    (hp : p ∈ centralFiltration omega hinv s) :
    scale a p * p⁻¹ ∈ centralFiltration omega hinv (r + s) := by
  have hp0 : p.first = 0 := hp.1
  refine ⟨by simp [hp0], ?_⟩
  have heq : (scale a p * p⁻¹).second = (a * c.bar a - 1) * p.second := by
    simp only [second_mul, second_scale, second_inv, first_scale, first_inv,
      hp0, mul_zero, map_neg, map_zero]
    have htrace := p.equation
    rw [hp0, zero_mul] at htrace
    linear_combination htrace
  rw [heq, omega.map_mul, WithTop.coe_add]
  exact add_le_add (norm_sub_one_ge omega hinv a r ha hdelta) hp.2

end Valuation

end Langlands.GroupScheme.SU3Root.Parameters
