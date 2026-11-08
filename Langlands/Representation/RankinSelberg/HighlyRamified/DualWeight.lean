import Langlands.Representation.RankinSelberg.HighlyRamified.DualTarget

/-!
# The weight of Jacquet–Shalika (4.4.18)

For a character `ω` of `F^×`, a level `f ≥ 1` and `v ∈ F^(m+1)` put
`φ(v) = ω(v_last)⁻¹` if `v_i ∈ 𝔭^f` for `i ≠ last` and `v_last` is an integral unit, and
`φ(v) = 0` otherwise. The weight of Jacquet and Shalika (1985), (4.4.18), is
`Φ₂(z) = φ(ϖ^c z)`.

* `φ` is invariant under translation by `(𝔭^f)^(m+1)` when `ω` is trivial on `1 + 𝔭^f`.
* At the vector `v_i = -(k⁻¹)_(rev i, 0)` attached to `k ∈ GL_(m+1)(O)`, `φ` equals
  `ω(-1)⁻¹ ω(k₀₀)` if `k ∈ K⁰(f)` and `0` otherwise.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- `x ∈ 𝔭^f`. -/
abbrev InPow (f : ℕ) (x : F) : Prop :=
  ∃ y : (ValuativeRel.valuation F).integer,
    y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (y : F) = x

/-- `x` is a unit of the integer ring. -/
abbrev IsIntegralUnit (x : F) : Prop :=
  x ≠ 0 ∧ x ∈ (ValuativeRel.valuation F).integer ∧ x⁻¹ ∈ (ValuativeRel.valuation F).integer

theorem InPow.add {f : ℕ} {x y : F} (hx : InPow f x) (hy : InPow f y) : InPow f (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, Ideal.add_mem _ ha hb, by push_cast; rfl⟩

theorem InPow.neg {f : ℕ} {x : F} (hx : InPow f x) : InPow f (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, neg_mem ha, by push_cast; rfl⟩

theorem InPow.sub {f : ℕ} {x y : F} (hx : InPow f x) (hy : InPow f y) : InPow f (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem InPow.integral_mul {f : ℕ} {a x : F} (ha : a ∈ (ValuativeRel.valuation F).integer)
    (hx : InPow f x) : InPow f (a * x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨a, ha⟩ * y, Ideal.mul_mem_left _ _ hy, rfl⟩

theorem InPow.integral {f : ℕ} {x : F} (hx : InPow f x) : x ∈ (ValuativeRel.valuation F).integer :=
  integer_of_mem_pow hx

/-- A product `a b = 1 + y` with `y` in the maximal ideal makes `b` an integral unit. -/
theorem isIntegralUnit_of_mul_eq {a b y : (ValuativeRel.valuation F).integer}
    (hy : y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer)
    (hab : a * b = 1 + y) : IsIntegralUnit (b : F) := by
  have hunit : IsUnit (a * b) := by
    rw [hab, show (1 : (ValuativeRel.valuation F).integer) + y = 1 - (-y) by ring]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hy))
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_right hunit
  have hne : (b : F) ≠ 0 := by
    intro h0
    rw [← hu] at h0
    simp at h0
  refine ⟨hne, b.property, ?_⟩
  have : ((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : F) = (b : F)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    have h1 := congrArg (fun z : (ValuativeRel.valuation F).integer => (z : F)) u.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at h1
    rw [← h1, hu]
  rw [← this]
  exact (u⁻¹ : (ValuativeRel.valuation F).integerˣ).val.property

/-- Adding an element of `𝔭^f`, `f ≥ 1`, to an integral unit gives an integral unit. -/
theorem IsIntegralUnit.add_inPow {f : ℕ} (hf : 0 < f) {x d : F} (hx : IsIntegralUnit x)
    (hd : InPow f d) : IsIntegralUnit (x + d) := by
  obtain ⟨y, hy, hye⟩ := hd.integral_mul hx.2.2
  have hym : y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer :=
    Ideal.pow_le_self hf.ne' hy
  have hxd : x + d ∈ (ValuativeRel.valuation F).integer := add_mem hx.2.1 hd.integral
  refine isIntegralUnit_of_mul_eq (a := ⟨x⁻¹, hx.2.2⟩) (b := ⟨x + d, hxd⟩) hym ?_
  apply Subtype.val_injective
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, hye]
  rw [mul_add, inv_mul_cancel₀ hx.1]

/-- The scaled weight `φ(v)` of (4.4.18). -/
def unitLastWeight (ω : Fˣ →* ℂˣ) (f : ℕ) (v : Fin (m + 1) → F) : ℂ := by
  classical
  exact if h : (∀ i : Fin (m + 1), i ≠ Fin.last m → InPow f (v i)) ∧
      IsIntegralUnit (v (Fin.last m)) then
    ((ω (Units.mk0 _ h.2.1) : ℂ))⁻¹ else 0

/-- The weight `Φ₂(z) = φ(ϖ^c z)` of Jacquet and Shalika (1985), (4.4.18). -/
def dualWeight (ω : Fˣ →* ℂˣ) (ϖ : F) (c f : ℕ) (z : Fin (m + 1) → F) : ℂ :=
  unitLastWeight ω f fun i => ϖ ^ c * z i

theorem unitLastWeight_of_cond (ω : Fˣ →* ℂˣ) {f : ℕ} {v : Fin (m + 1) → F}
    (h : (∀ i : Fin (m + 1), i ≠ Fin.last m → InPow f (v i)) ∧
      IsIntegralUnit (v (Fin.last m))) :
    unitLastWeight ω f v = ((ω (Units.mk0 _ h.2.1) : ℂ))⁻¹ := by
  unfold unitLastWeight
  split
  · rfl
  · contradiction

theorem unitLastWeight_of_not_cond (ω : Fˣ →* ℂˣ) {f : ℕ} {v : Fin (m + 1) → F}
    (h : ¬ ((∀ i : Fin (m + 1), i ≠ Fin.last m → InPow f (v i)) ∧
      IsIntegralUnit (v (Fin.last m)))) :
    unitLastWeight ω f v = 0 := by
  unfold unitLastWeight
  split
  · contradiction
  · rfl

/-- `φ` is invariant under translation by `(𝔭^f)^(m+1)`. -/
theorem unitLastWeight_add {ω : Fˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)
    (hω : TrivialOnPrincipalUnits ω f) (v d : Fin (m + 1) → F) (hd : ∀ i, InPow f (d i)) :
    unitLastWeight ω f (v + d) = unitLastWeight ω f v := by
  by_cases h : (∀ i : Fin (m + 1), i ≠ Fin.last m → InPow f (v i)) ∧
      IsIntegralUnit (v (Fin.last m))
  · have h' : (∀ i : Fin (m + 1), i ≠ Fin.last m → InPow f ((v + d) i)) ∧
        IsIntegralUnit ((v + d) (Fin.last m)) :=
      ⟨fun i hi => (h.1 i hi).add (hd i), h.2.add_inPow hf (hd _)⟩
    rw [unitLastWeight_of_cond ω h', unitLastWeight_of_cond ω h]
    congr 2
    apply omega_eq_of_sub_mem hω
    · simpa using h.2.2.2
    · obtain ⟨y, hy, hye⟩ := hd (Fin.last m)
      exact ⟨y, hy, by simp [hye]⟩
  · have h' : ¬ ((∀ i : Fin (m + 1), i ≠ Fin.last m → InPow f ((v + d) i)) ∧
        IsIntegralUnit ((v + d) (Fin.last m))) := by
      rintro ⟨h1, h2⟩
      apply h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := (h1 i hi).sub (hd i)
        simpa using this
      · have := h2.add_inPow hf (hd (Fin.last m)).neg
        simpa using this
    rw [unitLastWeight_of_not_cond ω h', unitLastWeight_of_not_cond ω h]

/-- `Φ₂` is invariant under translation by `O^(m+1)` once `ϖ^c O ⊆ 𝔭^f`. -/
theorem dualWeight_add {ω : Fˣ →* ℂˣ} {ϖ : F} {c f : ℕ} (hf : 0 < f)
    (hω : TrivialOnPrincipalUnits ω f)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F).integer, InPow f (ϖ ^ c * o))
    (z o : Fin (m + 1) → F) (ho : ∀ i, o i ∈ (ValuativeRel.valuation F).integer) :
    dualWeight ω ϖ c f (z + o) = dualWeight ω ϖ c f z := by
  unfold dualWeight
  have : (fun i => ϖ ^ c * (z + o) i) = (fun i => ϖ ^ c * z i) + fun i => ϖ ^ c * o i := by
    funext i
    simp [mul_add]
  rw [this, unitLastWeight_add hf hω _ _ fun i => hscale _ (ho i)]

/-- Integrality of every entry of `k` and `k⁻¹`. -/
abbrev IsIntegralMatrix (k : GeneralLinearGroup (Fin (m + 1)) F) : Prop :=
  (∀ i j, k i j ∈ (ValuativeRel.valuation F).integer) ∧
    ∀ i j, (k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) i j ∈ (ValuativeRel.valuation F).integer

theorem inFirstColumn_iff {f : ℕ} (k : GeneralLinearGroup (Fin (m + 1)) F) :
    InFirstColumn f k ↔ IsIntegralMatrix k ∧ ∀ j : Fin (m + 1), j ≠ 0 → InPow f (k j 0) := by
  rw [InFirstColumn, mem_firstColumnCongruence]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩

open Classical in
/-- The weight at the vector attached to `k ∈ GL_(m+1)(O)`:
`φ(-(k⁻¹)_(rev i, 0)) = ω(-1)⁻¹ ω(k₀₀)` on `K⁰(f)` and `0` off it. -/
theorem unitLastWeight_firstColumn {ω : Fˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)
    (hω : TrivialOnPrincipalUnits ω f) (k : GeneralLinearGroup (Fin (m + 1)) F)
    (hk : IsIntegralMatrix k) :
    unitLastWeight ω f (fun i => -(k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) i.rev 0) =
      if h : InFirstColumn f k then
        ((ω (-1) : ℂ))⁻¹ * (ω (firstEntryUnit hf k h) : ℂ) else 0 := by
  have hcond : ((∀ i : Fin (m + 1), i ≠ Fin.last m →
      InPow f (-(k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) i.rev 0)) ∧
      IsIntegralUnit (-(k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) (Fin.last m).rev 0)) ↔
      InFirstColumn f k := by
    constructor
    · rintro ⟨h1, -⟩
      have hkinv : InFirstColumn f k⁻¹ := by
        rw [inFirstColumn_iff]
        refine ⟨⟨hk.2, by simpa using hk.1⟩, fun j hj => ?_⟩
        have hj' : j.rev ≠ Fin.last m := by
          intro h
          apply hj
          rw [← Fin.rev_rev j, h, Fin.rev_last]
        have := (h1 j.rev hj').neg
        simpa using this
      simpa using inv_mem hkinv
    · intro h
      have hkinv : InFirstColumn f k⁻¹ := inv_mem h
      obtain ⟨-, hcol⟩ := (inFirstColumn_iff k⁻¹).1 hkinv
      refine ⟨fun i hi => (hcol i.rev ?_).neg, ?_⟩
      · intro h0
        apply hi
        rw [← Fin.rev_rev i, h0, Fin.rev_zero]
      · obtain ⟨hne, hint, hinv⟩ := firstColumn_entry_isUnit hf hkinv
        rw [Fin.rev_last]
        refine ⟨neg_ne_zero.mpr hne, neg_mem hint, ?_⟩
        rw [inv_neg]
        exact neg_mem hinv
  split_ifs with h
  · rw [unitLastWeight_of_cond ω (hcond.2 h)]
    have hkinv : InFirstColumn f k⁻¹ := inv_mem h
    obtain ⟨hne, -, hinv⟩ := firstColumn_entry_isUnit hf hkinv
    -- `ω((k⁻¹)₀₀) = ω(k₀₀)⁻¹`
    have hprod : ω (firstEntryUnit hf k⁻¹ hkinv * firstEntryUnit hf k h) = 1 := by
      apply hω
      obtain ⟨x, hx, hxe⟩ := firstColumn_entry_unit h
      exact ⟨x, hx, by simp [hxe]⟩
    have hsplit : Units.mk0 (-(k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) (Fin.last m).rev 0)
        (hcond.2 h).2.1 = (-1) * firstEntryUnit hf k⁻¹ hkinv := by
      ext
      simp [Fin.rev_last]
    rw [hsplit, map_mul, Units.val_mul, mul_inv]
    congr 1
    rw [map_mul, mul_eq_one_iff_eq_inv] at hprod
    rw [hprod, Units.val_inv_eq_inv_val, inv_inv]
  · rw [unitLastWeight_of_not_cond ω (fun h' => h (hcond.1 h'))]

end Langlands.RankinSelberg.HighlyRamified
