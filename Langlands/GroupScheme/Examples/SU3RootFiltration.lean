import Langlands.GroupScheme.Examples.SU3RootValuation

/-! # Actual valuation filtration subgroups of the SU3 coordinate group -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root.Parameters

universe u v
variable {L : Type u} {M : Type v} [Field L] [Field M]
  {c : RingInvolution L} {d : RingInvolution M}
  (omega : AddValuation L (WithTop ℝ))
  (hinv : ∀ z : L, omega (c.bar z) = omega z)

include hinv in
/-- Two first-coordinate bounds control the cross term in coordinate multiplication. -/
theorem crossTerm_ge (r s : ℝ) (x y : Parameters c)
    (hx : (r : WithTop ℝ) ≤ omega x.first) (hy : (s : WithTop ℝ) ≤ omega y.first) :
    (↑(r + s) : WithTop ℝ) ≤ omega (x.first * c.bar y.first) := by
  rw [omega.map_mul, hinv, WithTop.coe_add]
  exact add_le_add hx hy

/-- The root filtration at a real depth, with closure proved from the coordinates. -/
def filtration (r : ℝ) : Subgroup (Parameters c) where
  carrier := {x | (↑(2 * r) : WithTop ℝ) ≤ omega x.second}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change (↑(2 * r) : WithTop ℝ) ≤ omega (x * y).second
    rw [second_mul]
    apply omega.map_le_add (omega.map_le_add hx hy)
    have hx' := first_ge_of_second_ge omega hinv r x hx
    have hy' := first_ge_of_second_ge omega hinv r y hy
    simpa only [← two_mul] using crossTerm_ge omega hinv r r x y hx' hy'
  inv_mem' := by
    intro x hx
    change (↑(2 * r) : WithTop ℝ) ≤ omega x⁻¹.second
    rwa [second_inv, hinv]

@[simp] theorem mem_filtration (r : ℝ) (x : Parameters c) :
    x ∈ filtration omega hinv r ↔ (↑(2 * r) : WithTop ℝ) ≤ omega x.second := Iff.rfl

/-- The central filtration, considered as an actual subgroup of the whole coordinate group. -/
def centralFiltration (r : ℝ) : Subgroup (Parameters c) where
  carrier := {x | x.first = 0 ∧ (r : WithTop ℝ) ≤ omega x.second}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    refine ⟨by simp [hx.1, hy.1], ?_⟩
    change (r : WithTop ℝ) ≤ omega (x * y).second
    rw [second_mul, hx.1, zero_mul, add_zero]
    exact omega.map_le_add hx.2 hy.2
  inv_mem' := by
    intro x hx
    refine ⟨by simp [hx.1], ?_⟩
    change (r : WithTop ℝ) ≤ omega x⁻¹.second
    rw [second_inv, hinv]
    exact hx.2

@[simp] theorem mem_centralFiltration (r : ℝ) (x : Parameters c) :
    x ∈ centralFiltration omega hinv r ↔ x.first = 0 ∧ (r : WithTop ℝ) ≤ omega x.second := Iff.rfl

theorem mem_filtration_iff_depth (r : ℝ) (x : Parameters c) :
    x ∈ filtration omega hinv r ↔ (r : WithTop ℝ) ≤ depthA omega x :=
  (coe_le_halfTop_iff r (omega x.second)).symm

/-- Central thresholds use the literal inclusion of `central c` into the whole group. -/
theorem mem_centralFiltration_iff_depth (r : ℝ) (z : central c) :
    z.val ∈ centralFiltration omega hinv r ↔ (r : WithTop ℝ) ≤ depthDouble omega z := by
  simp only [mem_centralFiltration, (mem_central z.val).mp z.property, true_and, depthDouble]

/-- An ambient membership description which also records the central inclusion. -/
theorem mem_centralFiltration_iff_exists_depth (r : ℝ) (x : Parameters c) :
    x ∈ centralFiltration omega hinv r ↔
      ∃ z : central c, z.val = x ∧ (r : WithTop ℝ) ≤ depthDouble omega z := by
  constructor
  · intro hx
    exact ⟨⟨x, hx.1⟩, rfl, hx.2⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z.property, hz⟩

theorem first_ge_of_mem_filtration (r : ℝ) (x : Parameters c)
    (hx : x ∈ filtration omega hinv r) : (r : WithTop ℝ) ≤ omega x.first :=
  first_ge_of_second_ge omega hinv r x hx

/-- Larger real depths give smaller subgroups. -/
theorem filtration_antitone : Antitone (filtration omega hinv) := by
  intro r s hrs x hx
  exact (WithTop.coe_le_coe.mpr (by linarith : 2 * r ≤ 2 * s)).trans hx

theorem centralFiltration_antitone : Antitone (centralFiltration omega hinv) := by
  intro r s hrs x hx
  exact ⟨hx.1, (WithTop.coe_le_coe.mpr hrs).trans hx.2⟩

/-- The root filtration exhausts the actual group, including the identity. -/
theorem exists_mem_filtration (x : Parameters c) : ∃ r : ℝ, x ∈ filtration omega hinv r := by
  obtain ⟨r, hr⟩ := exists_real_le (depthA omega x)
  exact ⟨r, (mem_filtration_iff_depth omega hinv r x).mpr hr⟩

/-- The central filtration exhausts the literal central subgroup. -/
theorem exists_mem_centralFiltration (z : central c) :
    ∃ r : ℝ, z.val ∈ centralFiltration omega hinv r := by
  obtain ⟨r, hr⟩ := exists_real_le (depthDouble omega z)
  exact ⟨r, (mem_centralFiltration_iff_depth omega hinv r z).mpr hr⟩

/-- Elementwise separation of the root filtration. -/
theorem forall_mem_filtration_iff (x : Parameters c) :
    (∀ r : ℝ, x ∈ filtration omega hinv r) ↔ x = 1 := by
  simp only [mem_filtration_iff_depth, forall_real_le_iff, depthA_eq_top_iff]

/-- Elementwise separation, with the central filtration still in the ambient group. -/
theorem forall_mem_centralFiltration_iff (x : Parameters c) :
    (∀ r : ℝ, x ∈ centralFiltration omega hinv r) ↔ x = 1 := by
  constructor
  · intro hx
    have ht : omega x.second = ⊤ := (forall_real_le_iff _).mp (fun r => (hx r).2)
    exact (second_eq_zero_iff x).mp ((omega.top_iff).mp ht)
  · rintro rfl
    intro r
    exact (centralFiltration omega hinv r).one_mem

/-- Doubling the central depth is literal intersection with the root filtration. -/
theorem centralFiltration_double_eq_inf (r : ℝ) :
    centralFiltration omega hinv (2 * r) = central c ⊓ filtration omega hinv r := by
  ext x
  rfl

/-- The convention throughout is the ordered commutator `x*y*x⁻¹*y⁻¹`. -/
theorem commutator_mem_centralFiltration (r s : ℝ) (x y : Parameters c)
    (hx : x ∈ filtration omega hinv r) (hy : y ∈ filtration omega hinv s) :
    x * y * x⁻¹ * y⁻¹ ∈ centralFiltration omega hinv (r + s) := by
  obtain ⟨hfirst, hsecond⟩ := commutator_coordinates x y
  refine ⟨hfirst, ?_⟩
  rw [hsecond]
  have hx' := first_ge_of_mem_filtration omega hinv r x hx
  have hy' := first_ge_of_mem_filtration omega hinv s y hy
  apply omega.map_le_sub (crossTerm_ge omega hinv r s x y hx' hy')
  simpa only [add_comm s r] using crossTerm_ge omega hinv s r y x hy' hx'

variable (omega' : AddValuation M (WithTop ℝ))
  (hinv' : ∀ z : M, omega' (d.bar z) = omega' z)
  (f : L →+* M) (hf : ∀ z, f (c.bar z) = d.bar (f z))
  (hval : ∀ z, omega' (f z) = omega z)

include hval in
/-- Pullback along the published coordinate homomorphism preserves the root filtration. -/
theorem comap_filtration (r : ℝ) :
    (filtration omega' hinv' r).comap (map f hf) = filtration omega hinv r := by
  ext x
  change (↑(2 * r) : WithTop ℝ) ≤ omega' (f x.second) ↔
    (↑(2 * r) : WithTop ℝ) ≤ omega x.second
  rw [hval]

include hval in
/-- Field homomorphisms reflect zero first coordinate and preserve central thresholds. -/
theorem comap_centralFiltration (r : ℝ) :
    (centralFiltration omega' hinv' r).comap (map f hf) = centralFiltration omega hinv r := by
  ext x
  change (f x.first = 0 ∧ (r : WithTop ℝ) ≤ omega' (f x.second)) ↔
    (x.first = 0 ∧ (r : WithTop ℝ) ≤ omega x.second)
  rw [hval, map_eq_zero_iff f f.injective]

end Langlands.GroupScheme.SU3Root.Parameters
