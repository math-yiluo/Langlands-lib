import Langlands.Representation.RankinSelberg.HighlyRamified.DualEquivariance

/-!
# The averaging weight and the target function on `N_(m+1) K⁰(f)`

For a character `ω` of `F^×` trivial on `1 + 𝔭^f` and `f ≥ 1`:

* the weight `w(k) = ω(k₀₀)⁻¹` on `K⁰(f)`, zero elsewhere;
* the target `t(u k) = ψ_N(u) ω(k₀₀)` for `u ∈ N`, `k ∈ K⁰(f)`, zero off `N K⁰(f)`.

The value `ω(k₀₀)` only depends on `k₀₀` modulo `1 + 𝔭^f`, which makes both well defined and
locally constant.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- `ω` is trivial on `1 + 𝔭^f`. -/
def TrivialOnPrincipalUnits (ω : Fˣ →* ℂˣ) (f : ℕ) : Prop :=
  ∀ u : Fˣ, (∃ y : (ValuativeRel.valuation F).integer,
    y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (u : F) = 1 + y) →
    ω u = 1

/-- The entry `k₀₀` of `k ∈ K⁰(f)` as a unit, `f ≥ 1`. -/
def firstEntryUnit {f : ℕ} (hf : 0 < f) (k : GeneralLinearGroup (Fin (m + 1)) F)
    (hk : InFirstColumn f k) : Fˣ :=
  Units.mk0 (k 0 0) (firstColumn_entry_isUnit hf hk).1

@[simp] theorem firstEntryUnit_val {f : ℕ} (hf : 0 < f) (k : GeneralLinearGroup (Fin (m + 1)) F)
    (hk : InFirstColumn f k) : (firstEntryUnit hf k hk : F) = k 0 0 := rfl

/-- If two units differ by an element of `𝔭^f` and one has integral inverse, `ω` agrees on them. -/
theorem omega_eq_of_sub_mem {f : ℕ} {ω : Fˣ →* ℂˣ} (hω : TrivialOnPrincipalUnits ω f)
    {a b : Fˣ} (hb : ((b⁻¹ : Fˣ) : F) ∈ (ValuativeRel.valuation F).integer)
    (hab : ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (a : F) = b + y) :
    ω a = ω b := by
  obtain ⟨y, hy, hye⟩ := hab
  have h1 : ω (a * b⁻¹) = 1 := by
    apply hω
    refine ⟨⟨_, hb⟩ * y, Ideal.mul_mem_left _ _ hy, ?_⟩
    simp only [Units.val_mul, Subring.coe_mul, hye]
    rw [add_mul, Units.mul_inv]
    ring
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

/-- `(k l)₀₀ ≡ k₀₀` modulo `𝔭^f` for `k ∈ K⁰(f)` and `l` principal of level `f`. -/
theorem firstEntry_mul_principal {f : ℕ} {k l : GeneralLinearGroup (Fin (m + 1)) F}
    (hk : InFirstColumn f k)
    (hl : l ∈ Conductor.principalCongruenceSubgroup (ValuativeRel.valuation F).integer m
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f)) :
    ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (k * l : GeneralLinearGroup (Fin (m + 1)) F) 0 0 = k 0 0 + y := by
  classical
  obtain ⟨hint, -, -⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k).1 hk
  obtain ⟨hl1, -⟩ := (Conductor.principalCongruenceEntry F _ m _ l).1 hl
  choose y hy hye using hl1
  refine ⟨∑ j, ⟨_, hint 0 j⟩ * y j 0, Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j 0),
    ?_⟩
  change ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * l) 0 0 = _
  rw [Matrix.mul_apply]
  simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, hye]
  rw [show k 0 0 = ∑ j, k 0 j * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) j 0 by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; simp [Matrix.one_apply_ne hj]
    · simp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `(n k)₀₀ ≡ k₀₀` modulo `𝔭^f` for `k ∈ K⁰(f)` and integral upper unipotent `n`. -/
theorem firstEntry_unipotent_mul {f : ℕ} {k n : GeneralLinearGroup (Fin (m + 1)) F}
    (hk : InFirstColumn f k) (hn : n ∈ upperUnipotent (m + 1) F)
    (hnint : ∀ i j, n i j ∈ (ValuativeRel.valuation F).integer) :
    ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (n * k : GeneralLinearGroup (Fin (m + 1)) F) 0 0 = k 0 0 + y := by
  classical
  obtain ⟨-, -, hcol⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k).1 hk
  have hcol' : ∀ j : Fin (m + 1), ∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (x : F) = if j = 0 then 0 else k j 0 := by
    intro j
    by_cases hj : j = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [hj]⟩
    · obtain ⟨x, hx, hxe⟩ := hcol j hj
      exact ⟨x, hx, by simp [hj, hxe]⟩
  choose x hx hxe using hcol'
  refine ⟨∑ j, ⟨_, hnint 0 j⟩ * x j, Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j),
    ?_⟩
  change ((n : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * k) 0 0 = _
  rw [Matrix.mul_apply]
  have hn00 : n 0 0 = 1 := hn.2 0
  have hsplit : ∀ j, n 0 j * k j 0 =
      n 0 j * (if j = 0 then 0 else k j 0) + (if j = 0 then k 0 0 else 0) := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hn00]
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, hxe]
  ring

section Functions

variable (ω : Fˣ →* ℂˣ) {f : ℕ} (hf : 0 < f)

/-- The averaging weight `w(k) = ω(k₀₀)⁻¹` on `K⁰(f)`, zero elsewhere. -/
def firstColumnWeight (g : GeneralLinearGroup (Fin (m + 1)) F) : ℂ := by
  classical
  exact if h : InFirstColumn f g then ((ω (firstEntryUnit hf g h) : ℂ))⁻¹ else 0

/-- Its partner character `b(k) = ω(k₀₀)⁻¹` on `K⁰(f)`, one elsewhere. -/
def firstColumnCharacter (g : GeneralLinearGroup (Fin (m + 1)) F) : ℂ := by
  classical
  exact if h : InFirstColumn f g then ((ω (firstEntryUnit hf g h) : ℂ))⁻¹ else 1

theorem firstColumnWeight_of_mem {g : GeneralLinearGroup (Fin (m + 1)) F} (h : InFirstColumn f g) :
    firstColumnWeight ω hf g = ((ω (firstEntryUnit hf g h) : ℂ))⁻¹ := by
  simp [firstColumnWeight, h]

theorem firstColumnWeight_of_not_mem {g : GeneralLinearGroup (Fin (m + 1)) F}
    (h : ¬ InFirstColumn f g) : firstColumnWeight ω hf g = 0 := by
  simp [firstColumnWeight, h]

theorem firstColumnCharacter_of_mem {g : GeneralLinearGroup (Fin (m + 1)) F}
    (h : InFirstColumn f g) :
    firstColumnCharacter ω hf g = ((ω (firstEntryUnit hf g h) : ℂ))⁻¹ := by
  simp [firstColumnCharacter, h]

theorem firstColumnWeight_ne_zero {g : GeneralLinearGroup (Fin (m + 1)) F}
    (h : firstColumnWeight ω hf g ≠ 0) : InFirstColumn f g := by
  by_contra h'
  exact h (firstColumnWeight_of_not_mem ω hf h')

/-- `w b⁻¹` is the indicator of `K⁰(f)`. -/
theorem firstColumnWeight_mul_inv (g : GeneralLinearGroup (Fin (m + 1)) F) :
    firstColumnWeight ω hf g * (firstColumnCharacter ω hf g)⁻¹ =
      (firstColumnCongruence (ValuativeRel.valuation F).integer m
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f) :
          Set (GeneralLinearGroup (Fin (m + 1)) F)).indicator 1 g := by
  by_cases h : InFirstColumn f g
  · have hmem : g ∈ (firstColumnCongruence (ValuativeRel.valuation F).integer m
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f) :
          Set (GeneralLinearGroup (Fin (m + 1)) F)) := h
    rw [Set.indicator_of_mem hmem, firstColumnWeight_of_mem ω hf h,
      firstColumnCharacter_of_mem ω hf h, inv_inv, Pi.one_apply]
    exact inv_mul_cancel₀ (by simp)
  · have hmem : g ∉ (firstColumnCongruence (ValuativeRel.valuation F).integer m
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f) :
          Set (GeneralLinearGroup (Fin (m + 1)) F)) := h
    rw [Set.indicator_of_notMem hmem, firstColumnWeight_of_not_mem ω hf h, zero_mul]

variable {ω}

/-- The weight is right invariant under the principal congruence subgroup of level `f`. -/
theorem firstColumnWeight_mul_principal (hω : TrivialOnPrincipalUnits ω f)
    (g l : GeneralLinearGroup (Fin (m + 1)) F)
    (hl : l ∈ Conductor.principalCongruenceSubgroup (ValuativeRel.valuation F).integer m
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f)) :
    firstColumnWeight ω hf (g * l) = firstColumnWeight ω hf g := by
  have hlK : InFirstColumn f l :=
    principalCongruenceSubgroup_le_firstColumnCongruence _ m _ hl
  by_cases h : InFirstColumn f g
  · have hgl : InFirstColumn f (g * l) := mul_mem h hlK
    rw [firstColumnWeight_of_mem ω hf h, firstColumnWeight_of_mem ω hf hgl]
    congr 2
    apply omega_eq_of_sub_mem hω
    · simpa using (firstColumn_entry_isUnit hf h).2.2
    · simpa using firstEntry_mul_principal h hl
  · have hgl : ¬ InFirstColumn f (g * l) := fun h' => h (by
      simpa using mul_mem h' (inv_mem hlK))
    rw [firstColumnWeight_of_not_mem ω hf h, firstColumnWeight_of_not_mem ω hf hgl]

variable (ω)

/-- The target `t(u k) = ψ_N(u) ω(k₀₀)` on `N K⁰(f)`, zero elsewhere. -/
def firstColumnTarget (ψN : upperUnipotent (m + 1) F →* ℂˣ)
    (g : GeneralLinearGroup (Fin (m + 1)) F) : ℂ := by
  classical
  exact if h : ∃ u : upperUnipotent (m + 1) F, InFirstColumn f (u.val⁻¹ * g) then
    (ψN h.choose : ℂ) * ω (firstEntryUnit hf _ h.choose_spec) else 0

variable {ω}

theorem firstColumnTarget_of_not_mem (ψN : upperUnipotent (m + 1) F →* ℂˣ)
    {g : GeneralLinearGroup (Fin (m + 1)) F}
    (h : ¬ ∃ u : upperUnipotent (m + 1) F, InFirstColumn f (u.val⁻¹ * g)) :
    firstColumnTarget ω hf ψN g = 0 := by
  simp [firstColumnTarget, h]

/-- The defining values of the target on `N K⁰(f)`. -/
theorem firstColumnTarget_mul (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F).integer) → ψN n = 1)
    (u : upperUnipotent (m + 1) F) {k : GeneralLinearGroup (Fin (m + 1)) F}
    (hk : InFirstColumn f k) :
    firstColumnTarget ω hf ψN (u.val * k) = (ψN u : ℂ) * ω (firstEntryUnit hf k hk) := by
  classical
  have hex : ∃ u' : upperUnipotent (m + 1) F, InFirstColumn f (u'.val⁻¹ * (u.val * k)) :=
    ⟨u, by simpa using hk⟩
  simp only [firstColumnTarget]
  rw [dif_pos hex]
  set u' := hex.choose with hu'
  have hk' : InFirstColumn f (u'.val⁻¹ * (u.val * k)) := hex.choose_spec
  set n : upperUnipotent (m + 1) F := u'⁻¹ * u with hn
  have hnK : InFirstColumn f n.val := by
    have : n.val = (u'.val⁻¹ * (u.val * k)) * k⁻¹ := by
      simp [hn, mul_assoc]
    rw [this]
    exact mul_mem hk' (inv_mem hk)
  obtain ⟨hnint, -, -⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ n.val).1 hnK
  have hψn : ψN n = 1 := hψN n hnint
  have hu'eq : u' = u * n⁻¹ := by simp [hn]
  have hψ : (ψN u' : ℂ) = ψN u := by
    rw [hu'eq, map_mul, map_inv, hψn, inv_one, mul_one]
  have hω' : ω (firstEntryUnit hf _ hk') = ω (firstEntryUnit hf k hk) := by
    apply omega_eq_of_sub_mem hω
    · simpa using (firstColumn_entry_isUnit hf hk).2.2
    · obtain ⟨y, hy, hye⟩ := firstEntry_unipotent_mul hk n.property hnint
      refine ⟨y, hy, ?_⟩
      simp only [firstEntryUnit_val]
      rw [← hye, hn]
      simp [mul_assoc]
  rw [hψ, hω']

end Functions

section TargetProperties

variable {ω : Fˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

/-- Left `(N, ψ_N)`-equivariance of the target. -/
theorem firstColumnTarget_unipotent_mul (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F).integer) → ψN n = 1)
    (u : upperUnipotent (m + 1) F) (g : GeneralLinearGroup (Fin (m + 1)) F) :
    firstColumnTarget ω hf ψN (u.val * g) = (ψN u : ℂ) * firstColumnTarget ω hf ψN g := by
  by_cases h : ∃ u' : upperUnipotent (m + 1) F, InFirstColumn f (u'.val⁻¹ * g)
  · obtain ⟨u', hu'⟩ := h
    have hg : g = u'.val * (u'.val⁻¹ * g) := by simp
    rw [hg, ← mul_assoc, show u.val * u'.val = (u * u').val from rfl,
      firstColumnTarget_mul hf hω ψN hψN _ hu', firstColumnTarget_mul hf hω ψN hψN _ hu',
      map_mul, Units.val_mul]
    ring
  · have h' : ¬ ∃ u' : upperUnipotent (m + 1) F, InFirstColumn f (u'.val⁻¹ * (u.val * g)) := by
      rintro ⟨u', hu'⟩
      apply h
      refine ⟨u⁻¹ * u', ?_⟩
      simpa [mul_assoc] using hu'
    rw [firstColumnTarget_of_not_mem hf ψN h, firstColumnTarget_of_not_mem hf ψN h', mul_zero]

/-- The target is right invariant under the principal congruence subgroup of level `f`. -/
theorem firstColumnTarget_mul_principal (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F →* ℂˣ)
    (hψN : ∀ n : upperUnipotent (m + 1) F,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F).integer) → ψN n = 1)
    (g l : GeneralLinearGroup (Fin (m + 1)) F)
    (hl : l ∈ Conductor.principalCongruenceSubgroup (ValuativeRel.valuation F).integer m
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f)) :
    firstColumnTarget ω hf ψN (g * l) = firstColumnTarget ω hf ψN g := by
  have hlK : InFirstColumn f l :=
    principalCongruenceSubgroup_le_firstColumnCongruence _ m _ hl
  by_cases h : ∃ u : upperUnipotent (m + 1) F, InFirstColumn f (u.val⁻¹ * g)
  · obtain ⟨u, hu⟩ := h
    have hg : g = u.val * (u.val⁻¹ * g) := by simp
    have hgl : InFirstColumn f (u.val⁻¹ * g * l) := mul_mem hu hlK
    rw [hg, mul_assoc, firstColumnTarget_mul hf hω ψN hψN _ hgl,
      firstColumnTarget_mul hf hω ψN hψN _ hu]
    congr 2
    apply omega_eq_of_sub_mem hω
    · simpa using (firstColumn_entry_isUnit hf hu).2.2
    · simpa using firstEntry_mul_principal hu hl
  · have h' : ¬ ∃ u : upperUnipotent (m + 1) F, InFirstColumn f (u.val⁻¹ * (g * l)) := by
      rintro ⟨u, hu⟩
      apply h
      exact ⟨u, by simpa [mul_assoc] using mul_mem hu (inv_mem hlK)⟩
    rw [firstColumnTarget_of_not_mem hf ψN h, firstColumnTarget_of_not_mem hf ψN h']

/-- The target vanishes off `N K⁰(f)`. -/
theorem firstColumnTarget_support (ψN : upperUnipotent (m + 1) F →* ℂˣ)
    {g : GeneralLinearGroup (Fin (m + 1)) F} (hg : firstColumnTarget ω hf ψN g ≠ 0) :
    ∃ u : upperUnipotent (m + 1) F, InFirstColumn f (u.val * g) := by
  by_contra h
  apply hg
  apply firstColumnTarget_of_not_mem hf ψN
  rintro ⟨u, hu⟩
  exact h ⟨u⁻¹, by simpa using hu⟩

end TargetProperties

end Langlands.RankinSelberg.HighlyRamified
