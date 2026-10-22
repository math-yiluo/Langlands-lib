import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Max

/-! Finite upper breaks from the actual inertia fixed subspaces. -/

noncomputable section

namespace Langlands.Ramification.Padic

open Module
open scoped BigOperators Classical

universe uK uL uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (inertia T K) V)

/-- Dimension of the actual lower-group fixed subspace. -/
def inertiaFixedDimension (i : ℕ) : ℕ :=
  finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K i))

theorem inertiaLowerGroup_antitone : Antitone (inertiaLowerGroup T K) := by
  intro i j hij g hg
  exact lowerRamificationGroup_antitone T K hij hg

omit [FiniteDimensional ℂ V] in
theorem inertiaFixedVectors_monotone :
    Monotone (fun i => fixedVectors ρ (inertiaLowerGroup T K i)) := by
  intro i j hij v hv g
  exact hv ⟨g, inertiaLowerGroup_antitone T K hij g.property⟩

theorem inertiaFixedDimension_monotone : Monotone (inertiaFixedDimension T K ρ) := by
  intro i j hij
  exact Submodule.finrank_mono (inertiaFixedVectors_monotone T K ρ hij)

theorem inertiaFixedDimension_le_rank (i : ℕ) :
    inertiaFixedDimension T K ρ i ≤ finrank ℂ V :=
  Submodule.finrank_le _

omit [FiniteDimensional ℂ V] in
theorem inertiaFixedVectors_eq_top_of_lower_eq_bot {i : ℕ}
    (hi : lowerRamificationGroup T K i = ⊥) :
    fixedVectors ρ (inertiaLowerGroup T K i) = ⊤ := by
  ext v
  change (∀ g : inertiaLowerGroup T K i, ρ g v = v) ↔ True
  constructor
  · intro _; trivial
  · intro _ g
    have hg : (g : inertia T K) = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp (hi ▸ g.property)
    simp [hg]

omit [FiniteDimensional ℂ V] in
theorem inertiaFixedDimension_of_lower_eq_bot {i : ℕ}
    (hi : lowerRamificationGroup T K i = ⊥) :
    inertiaFixedDimension T K ρ i = finrank ℂ V := by
  rw [inertiaFixedDimension, inertiaFixedVectors_eq_top_of_lower_eq_bot T K ρ hi,
    finrank_top]

omit [FiniteDimensional ℂ V] in
theorem inertiaFixedDimension_of_cutoff {i : ℕ}
    (hi : ramificationCutoff T K ≤ i) :
    inertiaFixedDimension T K ρ i = finrank ℂ V :=
  inertiaFixedDimension_of_lower_eq_bot T K ρ
    (lowerRamificationGroup_eq_bot_of_cutoff T K i hi)

/-- Zero accounts for the entire tame and unramified part. A positive index
measures the increase from `G_i`-fixed to `G_(i+1)`-fixed vectors. -/
def lowerBreakMultiplicity (i : ℕ) : ℕ :=
  if i = 0 then inertiaFixedDimension T K ρ 1
  else inertiaFixedDimension T K ρ (i + 1) - inertiaFixedDimension T K ρ i

omit [FiniteDimensional ℂ V] in
@[simp] theorem lowerBreakMultiplicity_zero :
    lowerBreakMultiplicity T K ρ 0 = inertiaFixedDimension T K ρ 1 := by
  simp [lowerBreakMultiplicity]

omit [FiniteDimensional ℂ V] in
theorem lowerBreakMultiplicity_pos_index {i : ℕ} (hi : 0 < i) :
    lowerBreakMultiplicity T K ρ i =
      inertiaFixedDimension T K ρ (i + 1) - inertiaFixedDimension T K ρ i := by
  simp [lowerBreakMultiplicity, ne_of_gt hi]

omit [FiniteDimensional ℂ V] in
theorem lowerBreakMultiplicity_pos_iff {i : ℕ} (hi : 0 < i) :
    0 < lowerBreakMultiplicity T K ρ i ↔
      inertiaFixedDimension T K ρ i < inertiaFixedDimension T K ρ (i + 1) := by
  rw [lowerBreakMultiplicity_pos_index T K ρ hi, Nat.sub_pos_iff_lt]

theorem lowerBreakMultiplicity_eq_zero_of_lower_eq_bot {i : ℕ} (hi : 0 < i)
    (hbot : lowerRamificationGroup T K i = ⊥) :
    lowerBreakMultiplicity T K ρ i = 0 := by
  rw [lowerBreakMultiplicity_pos_index T K ρ hi,
    inertiaFixedDimension_of_lower_eq_bot T K ρ hbot]
  exact Nat.sub_eq_zero_of_le (inertiaFixedDimension_le_rank T K ρ (i + 1))

theorem lowerBreakMultiplicity_hasFiniteSupport :
    (lowerBreakMultiplicity T K ρ).HasFiniteSupport := by
  apply (Finset.range (ramificationCutoff T K + 1)).finite_toSet.subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hn
  have hle : ramificationCutoff T K + 1 ≤ i := Nat.le_of_not_gt hn
  exact hi (lowerBreakMultiplicity_eq_zero_of_lower_eq_bot T K ρ (by omega)
    (lowerRamificationGroup_eq_bot_of_cutoff T K i (by omega)))

/-- Intrinsic finite lower multiplicities: no truncation is part of the value. -/
def lowerBreakMultiplicities : ℕ →₀ ℕ :=
  Finsupp.ofSupportFinite _ (lowerBreakMultiplicity_hasFiniteSupport T K ρ)

@[simp] theorem lowerBreakMultiplicities_apply (i : ℕ) :
    lowerBreakMultiplicities T K ρ i = lowerBreakMultiplicity T K ρ i := rfl

/-- The partial sums telescope, including the full zero-break contribution. -/
theorem sum_lowerBreakMultiplicity_range (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), lowerBreakMultiplicity T K ρ i =
      inertiaFixedDimension T K ρ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      lowerBreakMultiplicity_pos_index T K ρ (Nat.succ_pos n)]
    exact Nat.add_sub_of_le (inertiaFixedDimension_monotone T K ρ (Nat.le_succ _))

/-- Any valid termination bound gives the same rank, including bound zero. -/
theorem sum_lowerBreakMultiplicity_of_bound (b : ℕ)
    (hb : lowerRamificationGroup T K b = ⊥) :
    ∑ i ∈ Finset.range (b + 1), lowerBreakMultiplicity T K ρ i = finrank ℂ V := by
  rw [sum_lowerBreakMultiplicity_range]
  apply inertiaFixedDimension_of_lower_eq_bot
  apply le_bot_iff.mp
  exact (lowerRamificationGroup_antitone T K (Nat.le_succ b)).trans (le_of_eq hb)

theorem sum_lowerBreakMultiplicities :
    (lowerBreakMultiplicities T K ρ).sum (fun _ m => m) = finrank ℂ V := by
  rw [Finsupp.sum]
  calc
    _ = ∑ i ∈ Finset.range (ramificationCutoff T K + 1),
        lowerBreakMultiplicity T K ρ i := by
      apply Finset.sum_subset
      · intro i hi
        simp only [Finsupp.mem_support_iff, lowerBreakMultiplicities_apply] at hi
        simp only [Finset.mem_range]
        by_contra hn
        exact hi (lowerBreakMultiplicity_eq_zero_of_lower_eq_bot T K ρ (by omega)
          (lowerRamificationGroup_eq_bot_of_cutoff T K i (by omega)))
      · intro i _ hi
        simpa only [Finsupp.mem_support_iff, lowerBreakMultiplicities_apply,
          not_not] using hi
    _ = _ := sum_lowerBreakMultiplicity_of_bound T K ρ _
      (lowerRamificationGroup_eq_bot_of_cutoff T K _ le_rfl)

/-- The actual Herbrand function embeds the nonnegative lower indices. -/
def upperBreakIndex : ℕ ↪ ℝ where
  toFun i := herbrandPhi T K i
  inj' := fun _ _ h => Nat.cast_injective ((herbrandPhi_strictMono T K).injective h)

@[simp] theorem upperBreakIndex_apply (i : ℕ) :
    upperBreakIndex T K i = herbrandPhi T K i := rfl

/-- Actual upper-break multiplicities, reindexed through Serre's phi. -/
def upperBreakMultiplicities : ℝ →₀ ℕ :=
  (lowerBreakMultiplicities T K ρ).embDomain (upperBreakIndex T K)

/-- The finite support of actual nonnegative upper breaks. -/
def upperBreakSupport : Finset ℝ := (upperBreakMultiplicities T K ρ).support

@[simp] theorem upperBreakMultiplicities_phi (i : ℕ) :
    upperBreakMultiplicities T K ρ (herbrandPhi T K i) =
      lowerBreakMultiplicity T K ρ i :=
  Finsupp.embDomain_apply_self _ _ _

@[simp] theorem upperBreakMultiplicities_zero :
    upperBreakMultiplicities T K ρ 0 = inertiaFixedDimension T K ρ 1 := by
  simpa using upperBreakMultiplicities_phi T K ρ 0

theorem upperBreakMultiplicities_of_not_range {r : ℝ}
    (hr : r ∉ Set.range (fun i : ℕ => herbrandPhi T K i)) :
    upperBreakMultiplicities T K ρ r = 0 :=
  Finsupp.embDomain_of_notMem_range _ _ _ hr

theorem mem_upperBreakSupport_iff {r : ℝ} :
    r ∈ upperBreakSupport T K ρ ↔ 0 < upperBreakMultiplicities T K ρ r := by
  simp only [upperBreakSupport, Finsupp.mem_support_iff, Nat.pos_iff_ne_zero]

theorem upperBreakSupport_eq_map :
    upperBreakSupport T K ρ =
      (lowerBreakMultiplicities T K ρ).support.map (upperBreakIndex T K) := rfl

theorem mem_upperBreakSupport_iff_exists {r : ℝ} :
    r ∈ upperBreakSupport T K ρ ↔
      ∃ i : ℕ, 0 < lowerBreakMultiplicity T K ρ i ∧ herbrandPhi T K i = r := by
  simp [upperBreakSupport_eq_map, Nat.pos_iff_ne_zero]

/-- Intrinsic support description, with the zero convention explicit. -/
theorem upperBreakSupport_description {r : ℝ} :
    r ∈ upperBreakSupport T K ρ ↔
      (r = 0 ∧ 0 < inertiaFixedDimension T K ρ 1) ∨
      ∃ i : ℕ, 0 < i ∧ herbrandPhi T K i = r ∧
        inertiaFixedDimension T K ρ i < inertiaFixedDimension T K ρ (i + 1) := by
  rw [mem_upperBreakSupport_iff_exists]
  constructor
  · rintro ⟨i, hi, hir⟩
    by_cases hz : i = 0
    · subst i
      exact Or.inl ⟨by simpa using hir.symm, by simpa using hi⟩
    · exact Or.inr ⟨i, Nat.pos_of_ne_zero hz, hir,
        (lowerBreakMultiplicity_pos_iff T K ρ (Nat.pos_of_ne_zero hz)).mp hi⟩
  · rintro (⟨rfl, hr⟩ | ⟨i, hi, hir, hd⟩)
    · exact ⟨0, by simpa using hr, by simp⟩
    · exact ⟨i, (lowerBreakMultiplicity_pos_iff T K ρ hi).mpr hd, hir⟩

/-- Any proved lower termination bound describes the same intrinsic support. -/
theorem mem_upperBreakSupport_iff_of_bound (b : ℕ)
    (hb : lowerRamificationGroup T K b = ⊥) {r : ℝ} :
    r ∈ upperBreakSupport T K ρ ↔
      ∃ i ∈ Finset.range (b + 1),
        0 < lowerBreakMultiplicity T K ρ i ∧ herbrandPhi T K i = r := by
  rw [mem_upperBreakSupport_iff_exists]
  constructor
  · rintro ⟨i, hi, hir⟩
    refine ⟨i, ?_, hi, hir⟩
    simp only [Finset.mem_range]
    by_contra hn
    have hbi : b ≤ i := by omega
    have hbot : lowerRamificationGroup T K i = ⊥ :=
      le_bot_iff.mp ((lowerRamificationGroup_antitone T K hbi).trans (le_of_eq hb))
    have hz := lowerBreakMultiplicity_eq_zero_of_lower_eq_bot T K ρ (by omega) hbot
    omega
  · rintro ⟨i, _, hi, hir⟩
    exact ⟨i, hi, hir⟩

theorem upperBreakSupport_nonneg {r : ℝ} (hr : r ∈ upperBreakSupport T K ρ) :
    0 ≤ r := by
  obtain ⟨i, _, rfl⟩ := (mem_upperBreakSupport_iff_exists T K ρ).mp hr
  simpa using (herbrandPhi_strictMono T K).monotone (Nat.cast_nonneg (α := ℝ) i)

theorem sum_upperBreakMultiplicities :
    (upperBreakMultiplicities T K ρ).sum (fun _ m => m) = finrank ℂ V := by
  simpa only [Finsupp.sum, upperBreakMultiplicities, Finsupp.support_embDomain,
    Finset.sum_map, Finsupp.embDomain_apply_self] using sum_lowerBreakMultiplicities T K ρ

theorem sum_upperBreakSupport :
    ∑ r ∈ upperBreakSupport T K ρ, upperBreakMultiplicities T K ρ r = finrank ℂ V :=
  sum_upperBreakMultiplicities T K ρ

theorem upperBreakSupport_nonempty_iff :
    (upperBreakSupport T K ρ).Nonempty ↔ 0 < finrank ℂ V := by
  rw [← sum_upperBreakSupport T K ρ, Finset.sum_pos_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, hr, (mem_upperBreakSupport_iff T K ρ).mp hr⟩
  · rintro ⟨r, hr, _⟩
    exact ⟨r, hr⟩

theorem upperBreakSupport_eq_empty_iff :
    upperBreakSupport T K ρ = ∅ ↔ finrank ℂ V = 0 := by
  rw [← Finset.not_nonempty_iff_eq_empty, upperBreakSupport_nonempty_iff]
  omega

/-- Wild-inertia-trivial representations have only the zero coefficient;
this includes representations trivial on all inertia. -/
theorem upperBreakMultiplicities_of_tame
    (ht : fixedVectors ρ (inertiaLowerGroup T K 1) = ⊤) :
    upperBreakMultiplicities T K ρ = Finsupp.single 0 (finrank ℂ V) := by
  have hd : inertiaFixedDimension T K ρ 1 = finrank ℂ V := by
    rw [inertiaFixedDimension, ht, finrank_top]
  have hdall (i : ℕ) (hi : 1 ≤ i) : inertiaFixedDimension T K ρ i = finrank ℂ V := by
    exact le_antisymm (inertiaFixedDimension_le_rank T K ρ i)
      (hd ▸ inertiaFixedDimension_monotone T K ρ hi)
  have hl : lowerBreakMultiplicities T K ρ = Finsupp.single 0 (finrank ℂ V) := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [hd]
    · rw [lowerBreakMultiplicities_apply,
        lowerBreakMultiplicity_pos_index T K ρ (Nat.pos_of_ne_zero hi),
        hdall i (by omega), hdall (i + 1) (by omega)]
      simp [hi]
  simp [upperBreakMultiplicities, hl, Finsupp.embDomain_single]

theorem upperBreakSupport_of_tame
    (ht : fixedVectors ρ (inertiaLowerGroup T K 1) = ⊤) (hv : 0 < finrank ℂ V) :
    upperBreakSupport T K ρ = {0} := by
  simp [upperBreakSupport, upperBreakMultiplicities_of_tame T K ρ ht, ne_of_gt hv]

theorem upperBreakSupport_of_trivial
    (ht : ∀ g : inertia T K, ρ g = LinearMap.id) (hv : 0 < finrank ℂ V) :
    upperBreakSupport T K ρ = {0} := by
  apply upperBreakSupport_of_tame T K ρ _ hv
  ext v
  change (∀ g : inertiaLowerGroup T K 1, ρ g v = v) ↔ True
  simp [ht]

/-- Invariants under the actual upper group, regarded inside finite inertia. -/
def inertiaUpperFixedVectors (r : ℝ) : Submodule ℂ V :=
  fixedVectors ρ ((upperRamificationGroup T K r).subgroupOf (inertia T K))

omit [FiniteDimensional ℂ V] in
theorem inertiaUpperFixedVectors_phi (i : ℕ) :
    inertiaUpperFixedVectors T K ρ (herbrandPhi T K i) =
      fixedVectors ρ (inertiaLowerGroup T K i) := by
  simp [inertiaUpperFixedVectors, inertiaLowerGroup]

theorem upperBreakIndex_lt_iff (i : ℕ) (r : ℝ) :
    herbrandPhi T K i < r ↔ i < ⌈herbrandPsi T K r⌉₊ := by
  rw [Nat.lt_ceil]
  simpa only [herbrandPhi_herbrandPsi] using
    ((herbrandPhi_strictMono T K).lt_iff_lt (a := (i : ℝ)) (b := herbrandPsi T K r))

omit [FiniteDimensional ℂ V] in
theorem inertiaUpperFixedVectors_eq_natceil {r : ℝ} (hr : 0 ≤ r) :
    inertiaUpperFixedVectors T K ρ r =
      fixedVectors ρ (inertiaLowerGroup T K ⌈herbrandPsi T K r⌉₊) := by
  have hp : 0 ≤ herbrandPsi T K r := by
    simpa using (herbrandPsi_strictMono T K).monotone hr
  have hg : upperRamificationGroup T K r =
      lowerRamificationGroup T K ⌈herbrandPsi T K r⌉₊ := by
    unfold upperRamificationGroup lowerRamificationGroupReal
    rw [← Int.natCast_ceil_eq_ceil hp]
    simpa only [lowerRamificationGroupReal, Int.ceil_natCast] using
      lowerRamificationGroupReal_nat T K ⌈herbrandPsi T K r⌉₊
  simp only [inertiaUpperFixedVectors, hg, inertiaLowerGroup]

/-- Left continuity requires the strict inequality on break indices. The
positive-threshold hypothesis excludes the deliberately aggregated zero term. -/
theorem sum_upperBreakSupport_lt {r : ℝ} (hr : 0 < r) :
    ∑ b ∈ (upperBreakSupport T K ρ).filter (fun b => b < r),
      upperBreakMultiplicities T K ρ b = finrank ℂ (inertiaUpperFixedVectors T K ρ r) := by
  have hn : 0 < ⌈herbrandPsi T K r⌉₊ := by
    simpa only [Nat.lt_ceil, Nat.cast_zero] using herbrandPsi_pos T K hr
  rw [upperBreakSupport_eq_map, Finset.filter_map, Finset.sum_map]
  simp only [Function.comp_def, upperBreakIndex_apply, upperBreakMultiplicities_phi,
    upperBreakIndex_lt_iff]
  calc
    _ = ∑ i ∈ Finset.range ⌈herbrandPsi T K r⌉₊, lowerBreakMultiplicity T K ρ i := by
      apply Finset.sum_subset
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i hi hnot
        have hni : i ∉ (lowerBreakMultiplicities T K ρ).support := by
          intro his
          exact hnot (Finset.mem_filter.mpr ⟨his, Finset.mem_range.mp hi⟩)
        simpa only [Finsupp.mem_support_iff, lowerBreakMultiplicities_apply,
          not_not] using hni
    _ = inertiaFixedDimension T K ρ ⌈herbrandPsi T K r⌉₊ := by
      obtain ⟨n, heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [heq]
      exact sum_lowerBreakMultiplicity_range T K ρ n
    _ = _ := by rw [inertiaUpperFixedVectors_eq_natceil T K ρ hr.le]; rfl

/-- Minimum upper break, available only when the actual support is nonempty. -/
def minimumUpperBreak (h : (upperBreakSupport T K ρ).Nonempty) : ℝ :=
  (upperBreakSupport T K ρ).min' h

/-- Maximum upper break, with the same explicit nonemptiness requirement. -/
def maximumUpperBreak (h : (upperBreakSupport T K ρ).Nonempty) : ℝ :=
  (upperBreakSupport T K ρ).max' h

variable (h : (upperBreakSupport T K ρ).Nonempty)

theorem minimumUpperBreak_mem :
    minimumUpperBreak T K ρ h ∈ upperBreakSupport T K ρ := Finset.min'_mem _ _

theorem maximumUpperBreak_mem :
    maximumUpperBreak T K ρ h ∈ upperBreakSupport T K ρ := Finset.max'_mem _ _

theorem minimumUpperBreak_le {r : ℝ} (hr : r ∈ upperBreakSupport T K ρ) :
    minimumUpperBreak T K ρ h ≤ r := Finset.min'_le _ _ hr

theorem le_maximumUpperBreak {r : ℝ} (hr : r ∈ upperBreakSupport T K ρ) :
    r ≤ maximumUpperBreak T K ρ h := Finset.le_max' _ _ hr

theorem minimumUpperBreak_le_maximumUpperBreak :
    minimumUpperBreak T K ρ h ≤ maximumUpperBreak T K ρ h :=
  Finset.min'_le_max' _ h

theorem minimumUpperBreak_nonneg : 0 ≤ minimumUpperBreak T K ρ h :=
  upperBreakSupport_nonneg T K ρ (minimumUpperBreak_mem T K ρ h)

theorem maximumUpperBreak_nonneg : 0 ≤ maximumUpperBreak T K ρ h :=
  upperBreakSupport_nonneg T K ρ (maximumUpperBreak_mem T K ρ h)

/-- Non-strict lower comparison, including equality at a break. -/
theorem le_minimumUpperBreak_iff (a : ℝ) :
    a ≤ minimumUpperBreak T K ρ h ↔ ∀ r ∈ upperBreakSupport T K ρ, a ≤ r :=
  Finset.le_min'_iff _ _

/-- Strict upper comparison: a vector at the largest break becomes fixed
only after that break in the left-continuous filtration. -/
theorem maximumUpperBreak_lt_iff (b : ℝ) :
    maximumUpperBreak T K ρ h < b ↔ ∀ r ∈ upperBreakSupport T K ρ, r < b :=
  Finset.max'_lt_iff _ _

theorem upperBreakMultiplicities_eq_zero_below_minimum {r : ℝ}
    (hr : r < minimumUpperBreak T K ρ h) : upperBreakMultiplicities T K ρ r = 0 := by
  by_contra hn
  exact (not_le_of_gt hr) (minimumUpperBreak_le T K ρ h
    ((mem_upperBreakSupport_iff T K ρ).mpr (Nat.pos_of_ne_zero hn)))

theorem upperBreakMultiplicities_eq_zero_above_maximum {r : ℝ}
    (hr : maximumUpperBreak T K ρ h < r) : upperBreakMultiplicities T K ρ r = 0 := by
  by_contra hn
  exact (not_le_of_gt hr) (le_maximumUpperBreak T K ρ h
    ((mem_upperBreakSupport_iff T K ρ).mpr (Nat.pos_of_ne_zero hn)))

/-- At positive thresholds the minimum bound is non-strict. -/
theorem le_minimumUpperBreak_iff_fixed_eq_bot {a : ℝ} (ha : 0 < a) :
    a ≤ minimumUpperBreak T K ρ h ↔ inertiaUpperFixedVectors T K ρ a = ⊥ := by
  rw [← Submodule.finrank_eq_zero, ← sum_upperBreakSupport_lt T K ρ ha,
    Finset.sum_eq_zero_iff, le_minimumUpperBreak_iff]
  constructor
  · intro hb r hr
    obtain ⟨hrs, hra⟩ := Finset.mem_filter.mp hr
    exact (not_lt_of_ge (hb r hrs) hra).elim
  · intro hz r hr
    by_contra hn
    have hzero := hz r (Finset.mem_filter.mpr ⟨hr, lt_of_not_ge hn⟩)
    exact (Nat.ne_of_gt ((mem_upperBreakSupport_iff T K ρ).mp hr)) hzero

/-- At positive thresholds complete fixedness is strictly above the maximum. -/
theorem maximumUpperBreak_lt_iff_fixed_eq_top {b : ℝ} (hb : 0 < b) :
    maximumUpperBreak T K ρ h < b ↔ inertiaUpperFixedVectors T K ρ b = ⊤ := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (upperBreakSupport T K ρ)
    (fun r => r < b) (fun r => upperBreakMultiplicities T K ρ r)
  rw [sum_upperBreakSupport T K ρ, sum_upperBreakSupport_lt T K ρ hb] at hsplit
  rw [maximumUpperBreak_lt_iff]
  constructor
  · intro hlt
    apply Submodule.eq_top_of_finrank_eq
    have hz : ∑ r ∈ (upperBreakSupport T K ρ).filter (fun r => ¬r < b),
        upperBreakMultiplicities T K ρ r = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      obtain ⟨hrs, hrb⟩ := Finset.mem_filter.mp hr
      exact (hrb (hlt r hrs)).elim
    omega
  · intro htop r hr
    have hdim : finrank ℂ (inertiaUpperFixedVectors T K ρ b) = finrank ℂ V := by
      rw [htop, finrank_top]
    have hz : ∑ r ∈ (upperBreakSupport T K ρ).filter (fun r => ¬r < b),
        upperBreakMultiplicities T K ρ r = 0 := by omega
    by_contra hn
    have hzero := (Finset.sum_eq_zero_iff.mp hz) r (Finset.mem_filter.mpr ⟨hr, hn⟩)
    exact (Nat.ne_of_gt ((mem_upperBreakSupport_iff T K ρ).mp hr)) hzero

end Langlands.Ramification.Padic
