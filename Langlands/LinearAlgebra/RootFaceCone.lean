import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! # Conic bounds from Levi-orthogonal root weights -/

noncomputable section

open Finset

namespace Langlands.LinearAlgebra.RootFaceCone

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (B : LinearMap.BilinForm ℝ E) (Φ : Finset E) (m : E → ℝ)

/-- The weight `ρ(y) = ∑_{α ∈ Φ, B α y > 0} m α • α` of the roots positive at `y`. -/
def rootWeight (y : E) : E :=
  ∑ α ∈ Φ.filter (fun α => 0 < B α y), m α • α

/-- The closed face of `y` for the hyperplanes `B α · = 0`, `α ∈ Φ`: the points where every
root vanishing at `y` vanishes and every other root has the weak sign it has at `y`. -/
def closedFace (y : E) : Set E :=
  {z | ∀ α ∈ Φ, (B α y = 0 → B α z = 0) ∧ (0 < B α y → 0 ≤ B α z) ∧
    (B α y < 0 → B α z ≤ 0)}

/-- The roots of `Φ` not vanishing at `y`. -/
def nonvanishingRoots (y : E) : Finset E :=
  Φ.filter (fun α => B α y ≠ 0)

variable {B Φ m}

theorem apply_eq_zero_of_mem_span {w z : E} (hw : w ∈ Submodule.span ℝ (Φ : Set E))
    (h : ∀ α ∈ Φ, B α z = 0) : B w z = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

/-- On the span of `Φ`, a positive definite form detects vectors by their root values. -/
theorem eq_zero_of_mem_span (hpos : ∀ x : E, x ≠ 0 → 0 < B x x) {z : E}
    (hz : z ∈ Submodule.span ℝ (Φ : Set E)) (h : ∀ α ∈ Φ, B α z = 0) : z = 0 := by
  by_contra hz0
  have := hpos z hz0
  rw [apply_eq_zero_of_mem_span hz h] at this
  exact lt_irrefl _ this

variable (B Φ m)

theorem rootWeight_mem_span (y : E) : rootWeight B Φ m y ∈ Submodule.span ℝ (Φ : Set E) :=
  Submodule.sum_mem _ fun _ hα =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_filter.1 hα).1))

/-- The weight depends only on which roots are positive. -/
theorem rootWeight_congr {y z : E} (h : ∀ α ∈ Φ, (0 < B α y ↔ 0 < B α z)) :
    rootWeight B Φ m y = rootWeight B Φ m z := by
  unfold rootWeight
  rw [Finset.filter_congr h]

theorem rootWeight_smul {t : ℝ} (ht : 0 < t) (y : E) :
    rootWeight B Φ m (t • y) = rootWeight B Φ m y := by
  apply rootWeight_congr
  intro α _
  rw [map_smul, smul_eq_mul]
  exact mul_pos_iff_of_pos_left ht

theorem rootWeight_apply (y z : E) :
    B (rootWeight B Φ m y) z = ∑ α ∈ Φ.filter (fun α => 0 < B α y), m α * B α z := by
  simp [rootWeight, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]

theorem mem_closedFace_self (y : E) : y ∈ closedFace B Φ y := fun _ _ =>
  ⟨id, le_of_lt, le_of_lt⟩

theorem smul_mem_closedFace {t : ℝ} (ht : 0 < t) (y : E) : t • y ∈ closedFace B Φ y := by
  intro α _
  simp only [map_smul, smul_eq_mul]
  exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_pos ht h).le,
    fun h => (mul_neg_of_pos_of_neg ht h).le⟩

variable {B Φ} in
theorem closedFace_subset {y z : E} (hz : z ∈ closedFace B Φ y) :
    closedFace B Φ z ⊆ closedFace B Φ y := by
  intro w hw α hα
  obtain ⟨h0, hp, hn⟩ := hz α hα
  obtain ⟨h0', hp', hn'⟩ := hw α hα
  refine ⟨fun h => h0' (h0 h), fun h => ?_, fun h => ?_⟩
  · rcases (hp h).eq_or_lt with h' | h'
    · exact (h0' h'.symm).ge
    · exact hp' h'
  · rcases (hn h).eq_or_lt with h' | h'
    · exact (h0' h').le
    · exact hn' h'

variable {B Φ m} in
/-- Some root of the symmetric family `Φ` is positive at a nonzero vector of its span. -/
theorem exists_pos_of_ne_zero (hpos : ∀ x : E, x ≠ 0 → 0 < B x x)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) {y : E} (hy : y ∈ Submodule.span ℝ (Φ : Set E)) (hy0 : y ≠ 0) :
    ∃ α ∈ Φ, 0 < B α y := by
  by_contra h
  push Not at h
  apply hy0
  refine eq_zero_of_mem_span hpos hy fun α hα => le_antisymm (h α hα) ?_
  have := h (-α) (hneg α hα)
  rw [map_neg, LinearMap.neg_apply] at this
  linarith

variable {B Φ m} in
/-- **Fixed points of the weight generate the closed faces.** Under Levi orthogonality
(`B α (ρ y) = 0` whenever `B α y = 0`), a linear functional which is nonnegative on every fixed
point `r = ρ(r)` of the closed face of a vector `y` of the span of `Φ` is nonnegative at `y`.
The statement is proved by strong induction on the number `n` of roots not vanishing at `y`. -/
theorem nonneg_of_nonneg_on_fixed
    (hpos : ∀ x : E, x ≠ 0 → 0 < B x x) (hneg : ∀ α ∈ Φ, -α ∈ Φ)
    (hm : ∀ α ∈ Φ, 0 < m α)
    (hlevi : ∀ y : E, ∀ α ∈ Φ, B α y = 0 → B α (rootWeight B Φ m y) = 0)
    (ψ : E →ₗ[ℝ] ℝ) (n : ℕ) :
    ∀ y : E, (nonvanishingRoots B Φ y).card = n →
      y ∈ Submodule.span ℝ (Φ : Set E) →
      (∀ r ∈ closedFace B Φ y, rootWeight B Φ m r = r → 0 ≤ ψ r) → 0 ≤ ψ y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hn hy hψ
  by_cases hy0 : y = 0
  · simp [hy0]
  set ρ := rootWeight B Φ m y with hρdef
  set N := nonvanishingRoots B Φ y with hNdef
  have hNne : N.Nonempty := by
    by_contra hN
    rw [Finset.not_nonempty_iff_eq_empty] at hN
    apply hy0
    refine eq_zero_of_mem_span hpos hy fun α hα => ?_
    by_contra h
    have : α ∈ N := Finset.mem_filter.2 ⟨hα, h⟩
    rw [hN] at this
    exact Finset.notMem_empty _ this
  let q : E → ℝ := fun α => B α ρ / B α y
  have hq : ∀ α ∈ N, B α ρ = q α * B α y := fun α hα =>
    (div_mul_cancel₀ _ (Finset.mem_filter.1 hα).2).symm
  have hzero : ∀ α ∈ Φ, B α y = 0 → B α ρ = 0 := hlevi y
  have hρspan : ρ ∈ Submodule.span ℝ (Φ : Set E) := rootWeight_mem_span B Φ m y
  obtain ⟨a1, ha1, hmin⟩ := N.exists_min_image q hNne
  obtain ⟨a2, ha2, hmax⟩ := N.exists_max_image q hNne
  rcases (hmin a2 ha2).eq_or_lt with heq | hlt
  · -- all quotients are equal: `ρ` is a positive multiple of `y`
    set l := q a1 with hl
    have hall : ∀ α ∈ Φ, B α (ρ - l • y) = 0 := by
      intro α hα
      rw [map_sub, map_smul, smul_eq_mul]
      by_cases hαy : B α y = 0
      · rw [hzero α hα hαy, hαy, mul_zero, sub_zero]
      · have hαN : α ∈ N := Finset.mem_filter.2 ⟨hα, hαy⟩
        have hqα : q α = l := le_antisymm (heq ▸ hmax α hαN) (hmin α hαN)
        rw [hq α hαN, hqα, sub_self]
    have hρ : ρ = l • y := sub_eq_zero.1 (eq_zero_of_mem_span hpos
      (Submodule.sub_mem _ hρspan (Submodule.smul_mem _ _ hy)) hall)
    have hpair : 0 < B ρ y := by
      rw [hρdef, rootWeight_apply]
      obtain ⟨β, hβ, hβpos⟩ := exists_pos_of_ne_zero hpos hneg hy hy0
      refine Finset.sum_pos (fun α hα => ?_) ⟨β, Finset.mem_filter.2 ⟨hβ, hβpos⟩⟩
      obtain ⟨hαΦ, hαpos⟩ := Finset.mem_filter.1 hα
      exact mul_pos (hm α hαΦ) hαpos
    have hlpos : 0 < l := by
      have h1 : B ρ y = l * B y y := by
        rw [hρ, map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h2 := hpos y hy0
      by_contra hl0
      push Not at hl0
      have : l * B y y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl0 h2.le
      linarith
    have hfix : rootWeight B Φ m ρ = ρ := by
      calc rootWeight B Φ m ρ = rootWeight B Φ m (l • y) := by rw [← hρ]
        _ = rootWeight B Φ m y := rootWeight_smul B Φ m hlpos y
        _ = ρ := rfl
    have hface : ρ ∈ closedFace B Φ y := hρ ▸ smul_mem_closedFace B Φ hlpos y
    have hψρ := hψ ρ hface hfix
    have hy' : y = l⁻¹ • ρ := by
      rw [hρ, smul_smul, inv_mul_cancel₀ hlpos.ne', one_smul]
    rw [hy', map_smul, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hlpos.le) hψρ
  · -- split `y` into two points of its closed face with more vanishing roots
    set d1 := ρ - q a1 • y with hd1
    set d2 := q a2 • y - ρ with hd2
    have hd1val : ∀ α ∈ N, B α d1 = (q α - q a1) * B α y := fun α hα => by
      rw [hd1, map_sub, map_smul, smul_eq_mul, hq α hα]
      ring
    have hd2val : ∀ α ∈ N, B α d2 = (q a2 - q α) * B α y := fun α hα => by
      rw [hd2, map_sub, map_smul, smul_eq_mul, hq α hα]
      ring
    have hface1 : d1 ∈ closedFace B Φ y := by
      intro α hα
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [hd1, map_sub, map_smul, smul_eq_mul, hzero α hα h, h, mul_zero, sub_zero]
      · have hαN : α ∈ N := Finset.mem_filter.2 ⟨hα, h.ne'⟩
        rw [hd1val α hαN]
        exact mul_nonneg (sub_nonneg.2 (hmin α hαN)) h.le
      · have hαN : α ∈ N := Finset.mem_filter.2 ⟨hα, h.ne⟩
        rw [hd1val α hαN]
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hmin α hαN)) h.le
    have hface2 : d2 ∈ closedFace B Φ y := by
      intro α hα
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [hd2, map_sub, map_smul, smul_eq_mul, hzero α hα h, h, mul_zero, sub_zero]
      · have hαN : α ∈ N := Finset.mem_filter.2 ⟨hα, h.ne'⟩
        rw [hd2val α hαN]
        exact mul_nonneg (sub_nonneg.2 (hmax α hαN)) h.le
      · have hαN : α ∈ N := Finset.mem_filter.2 ⟨hα, h.ne⟩
        rw [hd2val α hαN]
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hmax α hαN)) h.le
    have hcard : ∀ d ∈ closedFace B Φ y, ∀ a ∈ N, B a d = 0 →
        (nonvanishingRoots B Φ d).card < n := by
      intro d hd a ha had
      rw [← hn]
      refine Finset.card_lt_card ⟨fun α hα => ?_, fun h => ?_⟩
      · obtain ⟨hαΦ, hne⟩ := Finset.mem_filter.1 hα
        exact Finset.mem_filter.2 ⟨hαΦ, fun h => hne ((hd α hαΦ).1 h)⟩
      · exact (Finset.mem_filter.1 (h ha)).2 had
    have hc1 := hcard d1 hface1 a1 ha1 (by rw [hd1val a1 ha1, sub_self, zero_mul])
    have hc2 := hcard d2 hface2 a2 ha2 (by rw [hd2val a2 ha2, sub_self, zero_mul])
    have h1 := ih _ hc1 d1 rfl
      (Submodule.sub_mem _ hρspan (Submodule.smul_mem _ _ hy))
      (fun r hr hf => hψ r (closedFace_subset hface1 hr) hf)
    have h2 := ih _ hc2 d2 rfl
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) hρspan)
      (fun r hr hf => hψ r (closedFace_subset hface2 hr) hf)
    have hgap : 0 < q a2 - q a1 := sub_pos.2 hlt
    have hy' : y = (q a2 - q a1)⁻¹ • (d1 + d2) := by
      have hsum : d1 + d2 = (q a2 - q a1) • y := by
        rw [hd1, hd2, sub_smul]
        abel
      rw [hsum, smul_smul, inv_mul_cancel₀ hgap.ne', one_smul]
    rw [hy', map_smul, map_add, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hgap.le) (add_nonneg h1 h2)

/-- A uniform positive lower bound for the positive pairings between subset sums of `Φ` and
weighted subset sums of `Φ`. -/
theorem exists_pos_le_subsetSum_pairing :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T ∈ Φ.powerset, ∀ U ∈ Φ.powerset,
      0 < B (∑ α ∈ T, α) (∑ α ∈ U, m α • α) →
        ε ≤ B (∑ α ∈ T, α) (∑ α ∈ U, m α • α) := by
  classical
  let P : Finset ℝ := ((Φ.powerset ×ˢ Φ.powerset).image
    (fun p : Finset E × Finset E => B (∑ α ∈ p.1, α) (∑ α ∈ p.2, m α • α))).filter
      (fun x => 0 < x)
  have hmemP : ∀ T ∈ Φ.powerset, ∀ U ∈ Φ.powerset,
      0 < B (∑ α ∈ T, α) (∑ α ∈ U, m α • α) →
        B (∑ α ∈ T, α) (∑ α ∈ U, m α • α) ∈ P := fun T hT U hU hTU =>
    Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(T, U), Finset.mem_product.2 ⟨hT, hU⟩, rfl⟩, hTU⟩
  by_cases hP : P.Nonempty
  · exact ⟨P.min' hP, (Finset.mem_filter.1 (P.min'_mem hP)).2,
      fun T hT U hU hTU => P.min'_le _ (hmemP T hT U hU hTU)⟩
  · exact ⟨1, one_pos, fun T hT U hU hTU => (hP ⟨_, hmemP T hT U hU hTU⟩).elim⟩

variable {B Φ m}

/-- **The conic bound.** Let `B` be positive definite, `Φ = -Φ` finite with positive
multiplicities `m`, Levi orthogonal in the sense that `B α (ρ y) = 0` whenever `B α y = 0`, and
`S ⊆ Φ`. There is `ε > 0` such that for every `c ≥ 0` and every linear functional `H` with
`H r ≥ -c` at all fixed points `r = ρ(r)` with `B α r ≤ 0` for `α ∈ S`, every `ν` in the span
of `Φ` with `B α ν ≥ 0` for `α ∈ S` satisfies `H ν ≤ (c / ε) ∑_{α ∈ Φ} |B α ν|`. -/
theorem exists_pos_rootCone_bound
    (hpos : ∀ x : E, x ≠ 0 → 0 < B x x) (hneg : ∀ α ∈ Φ, -α ∈ Φ)
    (hm : ∀ α ∈ Φ, 0 < m α)
    (hlevi : ∀ y : E, ∀ α ∈ Φ, B α y = 0 → B α (rootWeight B Φ m y) = 0)
    (S : Finset E) (hS : S ⊆ Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, 0 ≤ c → ∀ H : E →ₗ[ℝ] ℝ,
      (∀ r : E, (∀ α ∈ S, B α r ≤ 0) → rootWeight B Φ m r = r → -c ≤ H r) →
      ∀ ν ∈ Submodule.span ℝ (Φ : Set E), (∀ α ∈ S, 0 ≤ B α ν) →
        H ν ≤ c / ε * ∑ α ∈ Φ, |B α ν| := by
  obtain ⟨ε, hε, hεle⟩ := exists_pos_le_subsetSum_pairing B Φ m
  refine ⟨ε, hε, fun c hc H hH ν hν hνS => ?_⟩
  have hcε : 0 ≤ c / ε := div_nonneg hc hε.le
  set y : E := -ν with hydef
  set T := Φ.filter (fun α => 0 < B α y) with hT
  set e : E := ∑ α ∈ T, α with he
  have he_apply : ∀ z : E, B e z = ∑ α ∈ T, B α z := fun z => by
    rw [he, map_sum, LinearMap.sum_apply]
  let ψ : E →ₗ[ℝ] ℝ := H + (c / ε) • B e
  have hψ_apply : ∀ z : E, ψ z = H z + c / ε * B e z := fun z => by
    simp only [ψ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hyspan : y ∈ Submodule.span ℝ (Φ : Set E) := Submodule.neg_mem _ hν
  have key := nonneg_of_nonneg_on_fixed hpos hneg hm hlevi ψ _ y rfl hyspan ?_
  · rw [hψ_apply, hydef, map_neg, map_neg] at key
    have hbound : -B e ν ≤ ∑ α ∈ Φ, |B α ν| := by
      rw [he_apply, ← Finset.sum_neg_distrib]
      calc ∑ α ∈ T, -B α ν ≤ ∑ α ∈ T, |B α ν| :=
            Finset.sum_le_sum fun α _ => neg_le_abs _
        _ ≤ ∑ α ∈ Φ, |B α ν| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => abs_nonneg _)
    have := mul_le_mul_of_nonneg_left hbound hcε
    linarith
  · intro r hr hfix
    by_cases hr0 : r = 0
    · simp [hr0]
    have hadm : ∀ α ∈ S, B α r ≤ 0 := fun α hα => by
      have hαΦ := hS hα
      have hyα : B α y ≤ 0 := by
        rw [hydef, map_neg]
        linarith [hνS α hα]
      rcases hyα.eq_or_lt with h | h
      · exact ((hr α hαΦ).1 h).le
      · exact (hr α hαΦ).2.2 h
    have hHr := hH r hadm hfix
    have hrspan : r ∈ Submodule.span ℝ (Φ : Set E) := hfix ▸ rootWeight_mem_span B Φ m r
    have hpos_er : 0 < B e r := by
      rw [he_apply]
      obtain ⟨β, hβ, hβpos⟩ := exists_pos_of_ne_zero hpos hneg hrspan hr0
      refine Finset.sum_pos' (fun α hα => ?_) ⟨β, ?_, hβpos⟩
      · obtain ⟨hαΦ, hαpos⟩ := Finset.mem_filter.1 hα
        exact (hr α hαΦ).2.1 hαpos
      · refine Finset.mem_filter.2 ⟨hβ, ?_⟩
        rcases lt_trichotomy (B β y) 0 with h | h | h
        · exact absurd ((hr β hβ).2.2 h) (not_le.2 hβpos)
        · exact absurd ((hr β hβ).1 h) hβpos.ne'
        · exact h
    have hε_er : ε ≤ B e r := by
      have h := hεle T (Finset.mem_powerset.2 (Finset.filter_subset _ _))
        (Φ.filter (fun α => 0 < B α r)) (Finset.mem_powerset.2 (Finset.filter_subset _ _))
      have hr' : (∑ α ∈ Φ.filter (fun α => 0 < B α r), m α • α) = r := hfix
      rw [hr', ← he] at h
      exact h hpos_er
    rw [hψ_apply]
    have hc' : c ≤ c / ε * B e r := by
      calc c = c / ε * ε := by field_simp
        _ ≤ c / ε * B e r := mul_le_mul_of_nonneg_left hε_er hcε
    linarith

/-- **The decay form of the conic bound.** With `ε` as in `exists_pos_rootCone_bound` and
`L = ∑_{α, β ∈ Φ} |B α β|`: if `B α ν ≥ s L` for every `α ∈ S`, then for every `β ∈ Φ`,
`H ν + s |H β| ≤ (c / ε) (∑_{α ∈ Φ} |B α ν| + s L)`. -/
theorem exists_pos_rootCone_decay
    (hpos : ∀ x : E, x ≠ 0 → 0 < B x x) (hneg : ∀ α ∈ Φ, -α ∈ Φ)
    (hm : ∀ α ∈ Φ, 0 < m α)
    (hlevi : ∀ y : E, ∀ α ∈ Φ, B α y = 0 → B α (rootWeight B Φ m y) = 0)
    (S : Finset E) (hS : S ⊆ Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ s : ℝ, 0 ≤ s → ∀ c : ℝ, 0 ≤ c →
      ∀ H : E →ₗ[ℝ] ℝ,
      (∀ r : E, (∀ α ∈ S, B α r ≤ 0) → rootWeight B Φ m r = r → -c ≤ H r) →
      ∀ ν ∈ Submodule.span ℝ (Φ : Set E), (∀ α ∈ S, s * L ≤ B α ν) →
        ∀ β ∈ Φ, H ν + s * |H β| ≤ c / ε * (∑ α ∈ Φ, |B α ν| + s * L) := by
  obtain ⟨ε, hε, hbound⟩ := exists_pos_rootCone_bound hpos hneg hm hlevi S hS
  set L : ℝ := ∑ α ∈ Φ, ∑ β ∈ Φ, |B α β| with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨ε, hε, L, hL0, fun s hs c hc H hH ν hν hνS β hβ => ?_⟩
  have hcε : 0 ≤ c / ε := div_nonneg hc hε.le
  -- the root values of `β` are bounded by `L`
  have hentry : ∀ α ∈ Φ, |B α β| ≤ L := fun α hα =>
    calc |B α β| ≤ ∑ β' ∈ Φ, |B α β'| :=
          Finset.single_le_sum (f := fun β' => |B α β'|) (fun _ _ => abs_nonneg _) hβ
      _ ≤ L := Finset.single_le_sum (f := fun α => ∑ β' ∈ Φ, |B α β'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hα
  have hcol : ∑ α ∈ Φ, |B α β| ≤ L := Finset.sum_le_sum fun α _ =>
    Finset.single_le_sum (f := fun β' => |B α β'|) (fun _ _ => abs_nonneg _) hβ
  have hgen : ∀ γ : E, γ ∈ Submodule.span ℝ (Φ : Set E) → (∀ α ∈ Φ, |B α γ| = |B α β|) →
      H ν + s * H γ ≤ c / ε * (∑ α ∈ Φ, |B α ν| + s * L) := by
    intro γ hγ hγabs
    have hν' : ν + s • γ ∈ Submodule.span ℝ (Φ : Set E) :=
      Submodule.add_mem _ hν (Submodule.smul_mem _ _ hγ)
    have hadm : ∀ α ∈ S, 0 ≤ B α (ν + s • γ) := fun α hα => by
      have hαΦ := hS hα
      rw [map_add, map_smul, smul_eq_mul]
      have h1 := hνS α hα
      have h2 : -L ≤ B α γ := by
        have := neg_abs_le (B α γ)
        rw [hγabs α hαΦ] at this
        linarith [hentry α hαΦ]
      nlinarith
    have hmain := hbound c hc H hH _ hν' hadm
    rw [map_add, map_smul, smul_eq_mul] at hmain
    have hsum : ∑ α ∈ Φ, |B α (ν + s • γ)| ≤ ∑ α ∈ Φ, |B α ν| + s * L := by
      calc ∑ α ∈ Φ, |B α (ν + s • γ)| ≤ ∑ α ∈ Φ, (|B α ν| + s * |B α β|) := by
            refine Finset.sum_le_sum fun α hα => ?_
            rw [map_add, map_smul, smul_eq_mul, ← hγabs α hα]
            calc |B α ν + s * B α γ| ≤ |B α ν| + |s * B α γ| := abs_add_le _ _
              _ = |B α ν| + s * |B α γ| := by rw [abs_mul, abs_of_nonneg hs]
        _ = ∑ α ∈ Φ, |B α ν| + s * ∑ α ∈ Φ, |B α β| := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ ∑ α ∈ Φ, |B α ν| + s * L := by
            have := mul_le_mul_of_nonneg_left hcol hs
            linarith
    have := mul_le_mul_of_nonneg_left hsum hcε
    linarith
  have hβspan : β ∈ Submodule.span ℝ (Φ : Set E) := Submodule.subset_span (Finset.mem_coe.2 hβ)
  rcases le_or_gt 0 (H β) with h | h
  · rw [abs_of_nonneg h]
    exact hgen β hβspan fun _ _ => rfl
  · have := hgen (-β) (Submodule.neg_mem _ hβspan) fun α _ => by rw [map_neg, abs_neg]
    rw [abs_of_neg h]
    rw [map_neg] at this
    exact this

end Langlands.LinearAlgebra.RootFaceCone
