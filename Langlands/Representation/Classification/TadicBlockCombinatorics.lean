import Langlands.Representation.Classification.TadicRectangleCombinatorics
import Langlands.Representation.Aubert.MultisegmentRankOrder
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof

/-!
# Rectangle decompositions of multisegments

Twisted rectangles `a(n,d)^(ν^α ρ)` with `ρ` unitary and `|α| < 1/2`, their Hermitian
reflection `α ↦ -α`, and uniqueness of a decomposition of a multisegment into such
rectangles.
-/

noncomputable section

namespace Langlands.Classification.TadicBlockCombinatorics

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-! ### Centered segments -/

/-- Two centered segments of unitary cuspidal data agree exactly when the data, the lengths
and the centers agree. -/
theorem tadicCenteredSegment_eq_iff {ρ τ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary)
    (hτ : τ.IsUnitary) {n v : ℕ} {hn : 0 < n} {hv : 0 < v} {x y : ℝ} :
    tadicCenteredSegment τ v hv x = tadicCenteredSegment ρ n hn y ↔ τ = ρ ∧ v = n ∧ x = y := by
  constructor
  · intro h
    have h' : (tadicCenteredSegment τ v hv x).twist 0 = tadicCenteredSegment ρ n hn y := by
      rw [Segment.twist_zero]; exact h
    obtain ⟨h1, h2, h3⟩ := tadicCenteredSegment_twist_eq hρ hτ h'
    exact ⟨h1, h2, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem tadicCenteredSegment_twist_base (ρ : T.CuspidalDatum.{uV, uF}) (d : ℕ) (hd : 0 < d)
    (α x : ℝ) : tadicCenteredSegment (ρ.twist α) d hd x = tadicCenteredSegment ρ d hd (α + x) := by
  simp only [tadicCenteredSegment, CuspidalDatum.twist_twist]
  congr 2
  ring

/-! ### Rectangle parameters -/

/-- Parameters `(ρ, n, d, α)` of the twisted rectangle `a(n,d)^(ν^α ρ)`. -/
structure RParam (T : F.TopologicalData) where
  ρ : T.CuspidalDatum.{uV, uF}
  n : ℕ
  d : ℕ
  hd : 0 < d
  α : ℝ

namespace RParam

/-- Admissible parameters: `ρ` unitary, `n > 0` and `|α| < 1/2`. -/
def Valid (q : RParam.{uF, uV} T) : Prop := q.ρ.IsUnitary ∧ 0 < q.n ∧ |q.α| < 1 / 2

/-- The rectangle `a(n,d)^(ν^α ρ)`. -/
def rect (q : RParam.{uF, uV} T) : T.Multisegment.{uV, uF} :=
  tadicMultisegment (q.ρ.twist q.α) q.n q.d q.hd

/-- The Hermitian reflection `α ↦ -α`. -/
def refl (q : RParam.{uF, uV} T) : RParam.{uF, uV} T := { q with α := -q.α }

@[simp] theorem refl_ρ (q : RParam.{uF, uV} T) : q.refl.ρ = q.ρ := rfl
@[simp] theorem refl_n (q : RParam.{uF, uV} T) : q.refl.n = q.n := rfl
@[simp] theorem refl_d (q : RParam.{uF, uV} T) : q.refl.d = q.d := rfl
@[simp] theorem refl_α (q : RParam.{uF, uV} T) : q.refl.α = -q.α := rfl

@[simp] theorem refl_refl (q : RParam.{uF, uV} T) : q.refl.refl = q := by
  cases q; simp [refl]

theorem Valid.refl {q : RParam.{uF, uV} T} (h : q.Valid) : q.refl.Valid :=
  ⟨h.1, h.2.1, by rw [refl_α, abs_neg]; exact h.2.2⟩

theorem ext' {q q' : RParam.{uF, uV} T} (hρ : q.ρ = q'.ρ) (hn : q.n = q'.n) (hd : q.d = q'.d)
    (hα : q.α = q'.α) : q = q' := by
  cases q; cases q'; simp_all

/-- The `j`-th segment of the rectangle, centered at `α + j - (n-1)/2`. -/
abbrev seg (q : RParam.{uF, uV} T) (j : ℕ) : T.Segment.{uV, uF} :=
  tadicCenteredSegment q.ρ q.d q.hd (q.α + ((j : ℝ) - ((q.n : ℝ) - 1) / 2))

theorem rect_eq (q : RParam.{uF, uV} T) : q.rect = (Multiset.range q.n).map q.seg := by
  unfold rect tadicMultisegment
  refine Multiset.map_congr rfl fun j _ => ?_
  exact tadicCenteredSegment_twist_base _ _ _ _ _

theorem mem_rect {q : RParam.{uF, uV} T} {Δ : T.Segment.{uV, uF}} :
    Δ ∈ q.rect ↔ ∃ j < q.n, q.seg j = Δ := by
  rw [rect_eq]
  simp

theorem card_rect (q : RParam.{uF, uV} T) : Multiset.card q.rect = q.n := by
  rw [rect_eq, Multiset.card_map, Multiset.card_range]

theorem rect_ne_zero {q : RParam.{uF, uV} T} (h : q.Valid) : q.rect ≠ 0 := by
  intro h0
  have := card_rect q
  rw [h0, Multiset.card_zero] at this
  exact (Nat.ne_of_gt h.2.1) this.symm

/-- The largest absolute center of the rectangle. -/
def width (q : RParam.{uF, uV} T) : ℝ := |q.α| + ((q.n : ℝ) - 1) / 2

theorem abs_center_le_width (q : RParam.{uF, uV} T) {j : ℕ} (hj : j < q.n) :
    |q.α + ((j : ℝ) - ((q.n : ℝ) - 1) / 2)| ≤ q.width := by
  have hj' : (j : ℝ) + 1 ≤ q.n := by exact_mod_cast hj
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold width
  rw [abs_le]
  constructor <;> cases abs_cases q.α <;> linarith

end RParam

/-! ### Uniqueness of rectangle decompositions -/

theorem mem_sum_map_iff {α β : Type*} {J : Multiset α} {f : α → Multiset β} {b : β} :
    b ∈ (J.map f).sum ↔ ∃ q ∈ J, b ∈ f q := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons q J ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.mem_add, ih]
    simp

open RParam in
/-- A segment of the sum of the rectangles of `J` is a segment of one of them. -/
theorem exists_center_of_mem_sum {J : Multiset (RParam.{uF, uV} T)} {Δ : T.Segment.{uV, uF}}
    (h : Δ ∈ (J.map RParam.rect).sum) : ∃ q ∈ J, ∃ j < q.n, q.seg j = Δ := by
  obtain ⟨q, hq, hΔ⟩ := mem_sum_map_iff.mp h
  obtain ⟨j, hj, rfl⟩ := mem_rect.mp hΔ
  exact ⟨q, hq, j, hj, rfl⟩

theorem nat_eq_of_real {n n' : ℕ} {α α' : ℝ} (h : α + ((n : ℝ) - 1) / 2 = α' + ((n' : ℝ) - 1) / 2)
    (hα : |α - α'| < 1 / 2) : n = n' := by
  rw [abs_lt] at hα
  have h1 : (n : ℝ) < n' + 1 := by linarith
  have h2 : (n' : ℝ) < n + 1 := by linarith
  have h1' : n < n' + 1 := by exact_mod_cast h1
  have h2' : n' < n + 1 := by exact_mod_cast h2
  omega

open RParam in
/-- The key step: a rectangle of maximal width in one decomposition occurs in every other
decomposition of the same multisegment. -/
theorem mem_of_sum_rect_eq_of_maximal {J J' : Multiset (RParam.{uF, uV} T)}
    (hJ : ∀ q ∈ J, q.Valid) (hJ' : ∀ q ∈ J', q.Valid)
    (hsum : (J.map RParam.rect).sum = (J'.map RParam.rect).sum) {q₀ : RParam.{uF, uV} T}
    (hq₀ : q₀ ∈ J) (hmax : ∀ q ∈ J, q.width ≤ q₀.width) : q₀ ∈ J' := by
  have hv₀ := hJ q₀ hq₀
  -- every segment of the common sum has absolute center at most `q₀.width`
  have hbound : ∀ q ∈ J', ∀ j < q.n, |q.α + ((j : ℝ) - ((q.n : ℝ) - 1) / 2)| ≤ q₀.width := by
    intro q hq j hj
    have hmem : q.seg j ∈ (J.map RParam.rect).sum := by
      rw [hsum]
      exact mem_sum_map_iff.mpr ⟨q, hq, mem_rect.mpr ⟨j, hj, rfl⟩⟩
    obtain ⟨r, hr, i, hi, hri⟩ := exists_center_of_mem_sum hmem
    have hv := hJ r hr
    have hv' := hJ' q hq
    obtain ⟨-, -, hc⟩ := (tadicCenteredSegment_eq_iff hv'.1 hv.1).mp hri
    rw [← hc]
    exact (abs_center_le_width r hi).trans (hmax r hr)
  have hn₀ : (0 : ℝ) ≤ ((q₀.n : ℝ) - 1) / 2 := by
    have : (1 : ℝ) ≤ q₀.n := by exact_mod_cast hv₀.2.1
    linarith
  rcases le_or_gt 0 q₀.α with hα | hα
  · -- the top segment of `q₀`
    have htop : q₀.seg (q₀.n - 1) ∈ (J'.map RParam.rect).sum := by
      rw [← hsum]
      exact mem_sum_map_iff.mpr ⟨q₀, hq₀,
        mem_rect.mpr ⟨q₀.n - 1, by have := hv₀.2.1; omega, rfl⟩⟩
    obtain ⟨q, hq, j, hj, hqj⟩ := exists_center_of_mem_sum htop
    have hv := hJ' q hq
    obtain ⟨hρ, hd, hc⟩ := (tadicCenteredSegment_eq_iff hv₀.1 hv.1).mp hqj
    have hcast : ((q₀.n - 1 : ℕ) : ℝ) = (q₀.n : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := hv₀.2.1; omega)]; simp
    rw [hcast] at hc
    have hw₀ : q₀.width = q₀.α + ((q₀.n : ℝ) - 1) / 2 := by
      unfold width; rw [abs_of_nonneg hα]
    have htopq := hbound q hq (q.n - 1) (by have := hv.2.1; omega)
    have hbotq := hbound q hq 0 hv.2.1
    have hcastq : ((q.n - 1 : ℕ) : ℝ) = (q.n : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := hv.2.1; omega)]; simp
    rw [hcastq] at htopq
    simp only [Nat.cast_zero] at hbotq
    rw [abs_le] at htopq hbotq
    have hj' : (j : ℝ) + 1 ≤ q.n := by exact_mod_cast hj
    have hqα : 0 ≤ q.α := by linarith
    have hαeq : q.α + ((q.n : ℝ) - 1) / 2 = q₀.α + ((q₀.n : ℝ) - 1) / 2 := by linarith
    have hα₀ := hv₀.2.2
    have hαq := hv.2.2
    rw [abs_of_nonneg hα] at hα₀
    rw [abs_of_nonneg hqα] at hαq
    have hn : q.n = q₀.n := nat_eq_of_real hαeq (by rw [abs_lt]; constructor <;> linarith)
    have hαe : q.α = q₀.α := by rw [hn] at hαeq; linarith
    have : q = q₀ := ext' hρ hn hd hαe
    rwa [this] at hq
  · -- the bottom segment of `q₀`
    have hbot : q₀.seg 0 ∈ (J'.map RParam.rect).sum := by
      rw [← hsum]
      exact mem_sum_map_iff.mpr ⟨q₀, hq₀, mem_rect.mpr ⟨0, hv₀.2.1, rfl⟩⟩
    obtain ⟨q, hq, j, hj, hqj⟩ := exists_center_of_mem_sum hbot
    have hv := hJ' q hq
    obtain ⟨hρ, hd, hc⟩ := (tadicCenteredSegment_eq_iff hv₀.1 hv.1).mp hqj
    simp only [Nat.cast_zero] at hc
    have hw₀ : q₀.width = -q₀.α + ((q₀.n : ℝ) - 1) / 2 := by
      unfold width; rw [abs_of_neg hα]
    have htopq := hbound q hq (q.n - 1) (by have := hv.2.1; omega)
    have hbotq := hbound q hq 0 hv.2.1
    have hcastq : ((q.n - 1 : ℕ) : ℝ) = (q.n : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := hv.2.1; omega)]; simp
    rw [hcastq] at htopq
    simp only [Nat.cast_zero] at hbotq
    rw [abs_le] at htopq hbotq
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hqα : q.α ≤ 0 := by linarith
    have hαeq : -q.α + ((q.n : ℝ) - 1) / 2 = -q₀.α + ((q₀.n : ℝ) - 1) / 2 := by linarith
    have hα₀ := hv₀.2.2
    have hαq := hv.2.2
    rw [abs_of_neg hα] at hα₀
    rw [abs_of_nonpos hqα] at hαq
    have hn : q.n = q₀.n := nat_eq_of_real hαeq (by rw [abs_lt]; constructor <;> linarith)
    have hαe : q.α = q₀.α := by rw [hn] at hαeq; linarith
    have : q = q₀ := ext' hρ hn hd hαe
    rwa [this] at hq

/-- **Uniqueness of rectangle decompositions.** Two multisets of admissible rectangle
parameters with the same sum of rectangles are equal. -/
theorem eq_of_sum_rect_eq : ∀ (k : ℕ) (J J' : Multiset (RParam.{uF, uV} T)),
    Multiset.card J = k → (∀ q ∈ J, q.Valid) → (∀ q ∈ J', q.Valid) →
      (J.map RParam.rect).sum = (J'.map RParam.rect).sum → J = J' := by
  classical
  intro k
  induction k with
  | zero =>
    intro J J' hk hJ hJ' hsum
    rw [Multiset.card_eq_zero] at hk
    subst hk
    rw [Multiset.map_zero, Multiset.sum_zero] at hsum
    by_contra hne
    obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero (Ne.symm hne)
    have := Multiset.sum_eq_zero_iff.mp hsum.symm q.rect (Multiset.mem_map_of_mem _ hq)
    exact RParam.rect_ne_zero (hJ' q hq) this
  | succ k ih =>
    intro J J' hk hJ hJ' hsum
    have hne : J ≠ 0 := by
      intro h; rw [h, Multiset.card_zero] at hk; omega
    obtain ⟨q₀, hq₀, hmax⟩ := Multiset.exists_max_image RParam.width hne
    have hq₀' := mem_of_sum_rect_eq_of_maximal hJ hJ' hsum hq₀ hmax
    rw [← Multiset.cons_erase hq₀, ← Multiset.cons_erase hq₀'] at hsum ⊢
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons] at hsum
    have hsum' := add_left_cancel hsum
    rw [ih (J.erase q₀) (J'.erase q₀) (by rw [Multiset.card_erase_of_mem hq₀, hk]; rfl)
      (fun q hq => hJ q (Multiset.mem_of_mem_erase hq))
      (fun q hq => hJ' q (Multiset.mem_of_mem_erase hq)) hsum']


/-! ### Hermitian reflection of segments -/

/-- A segment is *unitary-based* if its beginning is a real twist of a unitary cuspidal
datum (Tadić §2.3: every cuspidal datum is). -/
def UnitaryBased (Δ : T.Segment.{uV, uF}) : Prop :=
  ∃ (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ), ρ.IsUnitary ∧ Δ.base = ρ.twist x

open Classical in
/-- The Hermitian reflection `[ν^x ρ, ν^(x+l-1) ρ] ↦ [ν^(-(x+l-1)) ρ, ν^(-x) ρ]` of a
unitary-based segment; other segments are fixed. -/
def reflSeg (Δ : T.Segment.{uV, uF}) : T.Segment.{uV, uF} :=
  if h : UnitaryBased Δ then
    ⟨h.choose.twist (-(h.choose_spec.choose + ((Δ.length : ℝ) - 1))), Δ.length, Δ.length_pos⟩
  else Δ

theorem reflSeg_of_twist {ρ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary) (x : ℝ) (l : ℕ)
    (hl : 0 < l) :
    reflSeg (⟨ρ.twist x, l, hl⟩ : T.Segment.{uV, uF}) =
      ⟨ρ.twist (-(x + ((l : ℝ) - 1))), l, hl⟩ := by
  have h : UnitaryBased (⟨ρ.twist x, l, hl⟩ : T.Segment.{uV, uF}) := ⟨ρ, x, hρ, rfl⟩
  rw [reflSeg, dite_eq_left_of_eq_true (eq_true h)]
  have hspec := h.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := cuspidalDatum_eq_of_twist_eq_of_isUnitary hρ hspec.1 hspec.2.symm
  congr 1
  rw [h2, h1]

theorem reflSeg_tadicCenteredSegment {ρ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary)
    (d : ℕ) (hd : 0 < d) (c : ℝ) :
    reflSeg (tadicCenteredSegment ρ d hd c) = tadicCenteredSegment ρ d hd (-c) := by
  unfold tadicCenteredSegment
  rw [reflSeg_of_twist hρ]
  congr 2
  ring

theorem reflSeg_reflSeg (Δ : T.Segment.{uV, uF}) : reflSeg (reflSeg Δ) = Δ := by
  by_cases h : UnitaryBased Δ
  · obtain ⟨ρ, x, hρ, hb⟩ := h
    obtain ⟨b, l, hl⟩ := Δ
    simp only at hb
    subst hb
    rw [reflSeg_of_twist hρ, reflSeg_of_twist hρ]
    congr 2
    ring
  · have h' : reflSeg Δ = Δ := by rw [reflSeg, dite_eq_right_of_eq_false (eq_false h)]
    rw [h', h']

theorem count_map_reflSeg [DecidableEq (T.Segment.{uV, uF})] (a : T.Multisegment.{uV, uF})
    (Δ : T.Segment.{uV, uF}) : (a.map reflSeg).count Δ = a.count (reflSeg Δ) := by
  have hinj : Function.Injective (reflSeg (T := T)) :=
    Function.LeftInverse.injective reflSeg_reflSeg
  conv_lhs => rw [← reflSeg_reflSeg Δ]
  exact Multiset.count_map_eq_count' _ _ hinj _

/-- Count symmetry for all unitary-based segments makes a multisegment of unitary-based
segments reflection invariant. -/
theorem map_reflSeg_eq_of_count [DecidableEq (T.Segment.{uV, uF})] {a : T.Multisegment.{uV, uF}}
    (h : ∀ (ρ : T.CuspidalDatum.{uV, uF}), ρ.IsUnitary → ∀ (x : ℝ) (l : ℕ) (hl : 0 < l),
      a.count (⟨ρ.twist x, l, hl⟩ : T.Segment.{uV, uF}) =
        a.count (⟨ρ.twist (-(x + ((l : ℝ) - 1))), l, hl⟩ : T.Segment.{uV, uF})) :
    a.map reflSeg = a := by
  ext Δ
  rw [count_map_reflSeg]
  by_cases hΔ : UnitaryBased Δ
  · obtain ⟨ρ, x, hρ, hb⟩ := hΔ
    obtain ⟨b, l, hl⟩ := Δ
    simp only at hb
    subst hb
    rw [reflSeg_of_twist hρ]
    exact (h ρ hρ x l hl).symm
  · rw [reflSeg, dite_eq_right_of_eq_false (eq_false hΔ)]

namespace RParam

theorem seg_refl (q : RParam.{uF, uV} T) (hρ : q.ρ.IsUnitary) {j : ℕ} (hj : j < q.n) :
    reflSeg (q.seg j) = q.refl.seg (q.n - 1 - j) := by
  unfold seg
  rw [reflSeg_tadicCenteredSegment hρ]
  simp only [refl_ρ, refl_d, refl_n, refl_α]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem rect_refl (q : RParam.{uF, uV} T) (hρ : q.ρ.IsUnitary) :
    q.rect.map reflSeg = q.refl.rect := by
  classical
  rw [rect_eq, rect_eq, Multiset.map_map]
  have e : (Multiset.range q.n).map (reflSeg ∘ q.seg) =
      (Multiset.range q.n).map (q.refl.seg ∘ fun j => q.n - 1 - j) :=
    Multiset.map_congr rfl fun j hj => seg_refl q hρ (Multiset.mem_range.mp hj)
  rw [e, ← Multiset.map_map]
  congr 1
  have hnd : (Multiset.range q.n).Nodup := Multiset.nodup_range q.n
  have hinj : Set.InjOn (fun j => q.n - 1 - j) {j | j < q.n} := by
    intro i hi j hj hij
    simp only [Set.mem_ofPred_eq] at hi hj
    simp only at hij
    omega
  apply (Multiset.Nodup.ext ?_ hnd).mpr
  · intro j
    simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨q.n - 1 - j, by omega, by omega⟩
  · exact Multiset.Nodup.map_on (fun i hi j hj hij =>
      hinj (Multiset.mem_range.mp hi) (Multiset.mem_range.mp hj) hij) hnd

end RParam

theorem sum_rect_map_refl {J : Multiset (RParam.{uF, uV} T)} (hJ : ∀ q ∈ J, q.Valid) :
    ((J.map RParam.refl).map RParam.rect).sum = ((J.map RParam.rect).sum).map reflSeg := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons q J ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.sum_cons, Multiset.map_add,
      ih (fun r hr => hJ r (Multiset.mem_cons_of_mem hr)),
      RParam.rect_refl q (hJ q (Multiset.mem_cons_self q J)).1]

/-- **Hermitian pairing.** If a reflection-invariant multisegment is a sum of admissible
rectangles, the multiset of their parameters is reflection invariant. -/
theorem map_refl_eq_of_sum {J : Multiset (RParam.{uF, uV} T)} (hJ : ∀ q ∈ J, q.Valid)
    (h : ((J.map RParam.rect).sum).map reflSeg = (J.map RParam.rect).sum) :
    J.map RParam.refl = J := by
  refine eq_of_sum_rect_eq _ (J.map RParam.refl) J rfl ?_ hJ ?_
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    exact (hJ r hr).refl
  · rw [sum_rect_map_refl hJ, h]


/-! ### Unitary-based segments -/

open GeneralLinear in
/-- Tadić §2.3: every cuspidal datum is a real twist of a unitary one. -/
theorem exists_unitary_twist (ρ : T.CuspidalDatum.{max uF uV, uF}) :
    ∃ (ρ₀ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ), ρ₀.IsUnitary ∧ ρ = ρ₀.twist x := by
  let := T.topology
  obtain ⟨r, hr, c⟩ := ρ
  induction c using Quotient.inductionOn with
  | h A =>
    obtain ⟨t, hB, hcls⟩ := supercuspidalRepRealUnitarization.{uF, max uF uV} F T r hr A
    let ρ' : T.CuspidalDatum.{max uF uV, uF} := ⟨r, hr, Quotient.mk _ A⟩
    have h1 : (ρ'.twist t) = ⟨r, hr, (SupercuspidalRep.twist (T.determinantPowerCharacter r t)
        (T.isOpen_ker_determinantPowerCharacter r t)
        (T.ker_determinant_le_ker_determinantPowerCharacter r t) A).isoClass⟩ := by
      change (⟨r, hr, T.supercuspidalClassRealPowerTwist r t (Quotient.mk _ A)⟩ :
        T.CuspidalDatum.{max uF uV, uF}) = _
      rw [hcls]
      rfl
    refine ⟨ρ'.twist t, -t, ?_, ?_⟩
    · rw [h1]; exact hB
    · rw [CuspidalDatum.twist_twist, neg_add_cancel, CuspidalDatum.twist_zero]

theorem unitaryBased (Δ : T.Segment.{max uF uV, uF}) : UnitaryBased Δ := by
  obtain ⟨ρ, x, hρ, h⟩ := exists_unitary_twist Δ.base
  exact ⟨ρ, x, hρ, h⟩

/-! ### Extension of segments -/

/-- `ν^(-1/2)` times the segment extended by one: `[ν^(x-1/2) ρ, ν^(x+l-1/2) ρ]` for
`Δ = [ν^x ρ, ν^(x+l-1) ρ]`; it inverts `Δ ↦ ν^(1/2) Δ⁻` on segments of length at least two. -/
def extSeg (Δ : T.Segment.{uV, uF}) : T.Segment.{uV, uF} :=
  ⟨Δ.base.twist (-(1 / 2)), Δ.length + 1, Nat.succ_pos _⟩

theorem extSeg_tadicCenteredSegment (ρ : T.CuspidalDatum.{uV, uF}) (d : ℕ) (hd : 0 < d)
    (c : ℝ) : extSeg (tadicCenteredSegment ρ d hd c) =
      tadicCenteredSegment ρ (d + 1) (Nat.succ_pos d) c := by
  simp only [extSeg, tadicCenteredSegment, CuspidalDatum.twist_twist]
  congr 2
  push_cast
  ring

/-- Every multisegment is the extension of `ν^(1/2) a⁻` plus its one-element segments. -/
theorem eq_extSeg_dropLast_add (a : T.Multisegment.{uV, uF}) :
    a = ((Multisegment.dropLast a).twist (1 / 2)).map extSeg +
      a.filter (fun Δ => Δ.length = 1) := by
  induction a using Multiset.induction_on with
  | empty => simp [Multisegment.twist]
  | cons Δ a ih =>
    by_cases h : 1 < Δ.length
    · rw [Multisegment.dropLast_cons_of_one_lt Δ h, Multisegment.twist, Multiset.map_cons,
        Multiset.map_cons, Multiset.filter_cons_of_neg (p := fun Δ : T.Segment.{uV, uF} => Δ.length = 1) _ (by omega), Multiset.cons_add]
      conv_lhs => rw [ih]
      congr 1
      · obtain ⟨b, l, hl⟩ := Δ
        simp only [extSeg, Segment.twist, Segment.dropLastNonempty, CuspidalDatum.twist_twist]
        simp only at h
        congr 1
        · norm_num
        · omega
    · have h1 : Δ.length = 1 := by have := Δ.length_pos; omega
      rw [Multisegment.dropLast_cons_of_length_eq_one Δ h1, Multiset.filter_cons_of_pos (p := fun Δ : T.Segment.{uV, uF} => Δ.length = 1) _ h1,
        Multiset.add_cons]
      conv_lhs => rw [ih]

namespace RParam

/-- The rectangle with segments one longer. -/
def ext (q : RParam.{uF, uV} T) : RParam.{uF, uV} T :=
  { q with d := q.d + 1, hd := Nat.succ_pos _ }

theorem rect_map_extSeg (q : RParam.{uF, uV} T) : q.rect.map extSeg = q.ext.rect := by
  rw [rect_eq, rect_eq, Multiset.map_map]
  exact Multiset.map_congr rfl fun j _ => extSeg_tadicCenteredSegment _ _ _ _

end RParam

/-! ### One-element segments -/

theorem range_succ_eq_cons_map (n : ℕ) :
    Multiset.range (n + 1) = 0 ::ₘ (Multiset.range n).map Nat.succ := by
  change ((List.range (n + 1) : List ℕ) : Multiset ℕ) = _
  rw [List.range_succ_eq_map]
  rfl

/-- The one-element segment `{ν^x ρ}`. -/
abbrev pt (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) : T.Segment.{uV, uF} :=
  tadicCenteredSegment ρ 1 Nat.one_pos x

/-- The one-element rectangle parameters `a(n,1)^(ν^α ρ)`. -/
def stParam (ρ : T.CuspidalDatum.{uV, uF}) (n : ℕ) (α : ℝ) : RParam.{uF, uV} T :=
  ⟨ρ, n, 1, Nat.one_pos, α⟩

theorem stParam_seg (ρ : T.CuspidalDatum.{uV, uF}) (n : ℕ) (α : ℝ) (j : ℕ) :
    (stParam ρ n α).seg j = pt ρ (α + ((j : ℝ) - ((n : ℝ) - 1) / 2)) := rfl

/-- `a(m+2,1)^ρ = {ν^((m+1)/2) ρ} + {ν^(-(m+1)/2) ρ} + a(m,1)^ρ`. -/
theorem stParam_rect_succ_succ (ρ : T.CuspidalDatum.{uV, uF}) (m : ℕ) :
    (stParam ρ (m + 2) 0).rect =
      pt ρ (((m : ℝ) + 1) / 2) ::ₘ pt ρ (-(((m : ℝ) + 1) / 2)) ::ₘ (stParam ρ m 0).rect := by
  rw [RParam.rect_eq, RParam.rect_eq]
  change Multiset.map _ (Multiset.range (m + 1 + 1)) = _ ::ₘ _ ::ₘ Multiset.map _ (Multiset.range m)
  rw [range_succ_eq_cons_map, Multiset.range_succ,
    Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_map]
  have e1 : (stParam ρ (m + 2) 0).seg 0 = pt ρ (-(((m : ℝ) + 1) / 2)) := by
    rw [stParam_seg]; congr 1; push_cast; ring
  have e2 : (stParam ρ (m + 2) 0).seg (Nat.succ m) = pt ρ (((m : ℝ) + 1) / 2) := by
    rw [stParam_seg]; congr 1; push_cast; ring
  have e3 : (Multiset.range m).map ((stParam ρ (m + 2) 0).seg ∘ Nat.succ) =
      (Multiset.range m).map (stParam ρ m 0).seg :=
    Multiset.map_congr rfl fun j _ => by
      simp only [Function.comp, stParam_seg]; congr 1; push_cast; ring
  rw [e1, e2, e3, Multiset.cons_swap]

/-- `a(k+1,1)^(ν^α ρ) = {ν^(α+k/2) ρ} + a(k,1)^(ν^(α-1/2) ρ)`. -/
theorem stParam_rect_succ_top (ρ : T.CuspidalDatum.{uV, uF}) (k : ℕ) (α : ℝ) :
    (stParam ρ (k + 1) α).rect = pt ρ (α + (k : ℝ) / 2) ::ₘ (stParam ρ k (α - 1 / 2)).rect := by
  rw [RParam.rect_eq, RParam.rect_eq]
  change Multiset.map _ (Multiset.range (k + 1)) = _ ::ₘ Multiset.map _ (Multiset.range k)
  rw [Multiset.range_succ, Multiset.map_cons]
  congr 1
  · rw [stParam_seg]; congr 1; push_cast; ring
  · exact Multiset.map_congr rfl fun j _ => by rw [stParam_seg, stParam_seg]; congr 1; push_cast; ring

/-- `a(k+1,1)^(ν^(-α) ρ) = {ν^(-(α+k/2)) ρ} + a(k,1)^(ν^(1/2-α) ρ)`. -/
theorem stParam_rect_succ_bot (ρ : T.CuspidalDatum.{uV, uF}) (k : ℕ) (α : ℝ) :
    (stParam ρ (k + 1) (-α)).rect =
      pt ρ (-(α + (k : ℝ) / 2)) ::ₘ (stParam ρ k (1 / 2 - α)).rect := by
  rw [RParam.rect_eq, RParam.rect_eq]
  change Multiset.map _ (Multiset.range (k + 1)) = _ ::ₘ Multiset.map _ (Multiset.range k)
  rw [range_succ_eq_cons_map, Multiset.map_cons, Multiset.map_map]
  congr 1
  · rw [stParam_seg]; congr 1; push_cast; ring
  · exact Multiset.map_congr rfl fun j _ => by
      simp only [Function.comp, stParam_seg]; congr 1; push_cast; ring


theorem stParam_rect_one (ρ : T.CuspidalDatum.{uV, uF}) (α : ℝ) :
    (stParam ρ 1 α).rect = {pt ρ α} := by
  rw [RParam.rect_eq]
  change Multiset.map _ (Multiset.range (0 + 1)) = _
  rw [Multiset.range_succ, Multiset.range_zero, Multiset.map_cons, Multiset.map_zero, stParam_seg,
    Multiset.cons_zero]
  congr 2
  push_cast
  ring

theorem stParam_rect_zero (ρ : T.CuspidalDatum.{uV, uF}) (α : ℝ) :
    (stParam ρ 0 α).rect = 0 := by
  rw [RParam.rect_eq]
  rfl

theorem stParam_refl (ρ : T.CuspidalDatum.{uV, uF}) (n : ℕ) (α : ℝ) :
    (stParam ρ n α).refl = stParam ρ n (-α) := rfl

/-! ### Reflection-invariant families of one-element rectangles -/

/-- A reflection-invariant multiset of admissible parameters with `d = 1`. -/
def StFamily (J : Multiset (RParam.{uF, uV} T)) : Prop :=
  (∀ q ∈ J, q.Valid ∧ q.d = 1) ∧ J.map RParam.refl = J

theorem StFamily.zero : StFamily (0 : Multiset (RParam.{uF, uV} T)) :=
  ⟨fun q hq => absurd hq (Multiset.notMem_zero q), rfl⟩

theorem StFamily.add {J J' : Multiset (RParam.{uF, uV} T)} (h : StFamily J)
    (h' : StFamily J') : StFamily (J + J') :=
  ⟨fun q hq => (Multiset.mem_add.mp hq).elim (h.1 q) (h'.1 q), by
    rw [Multiset.map_add, h.2, h'.2]⟩

theorem StFamily.single {ρ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary) {n : ℕ}
    (hn : 0 < n) : StFamily ({stParam ρ n 0} : Multiset (RParam.{uF, uV} T)) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq
    subst hq
    exact ⟨⟨hρ, hn, show |(0 : ℝ)| < 1 / 2 by norm_num⟩, rfl⟩
  · rw [Multiset.map_singleton, stParam_refl, neg_zero]

theorem StFamily.pair {ρ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary) {n : ℕ}
    (hn : 0 < n) {α : ℝ} (hα : |α| < 1 / 2) :
    StFamily ({stParam ρ n α, stParam ρ n (-α)} : Multiset (RParam.{uF, uV} T)) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨hρ, hn, hα⟩, rfl⟩
    · exact ⟨⟨hρ, hn, show |(-α)| < 1 / 2 by rw [abs_neg]; exact hα⟩, rfl⟩
  · rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, stParam_refl,
      stParam_refl, neg_neg, ← Multiset.cons_zero, ← Multiset.cons_zero, Multiset.cons_swap]

/-- **The pair identity.** For `y > 0` and unitary `ρ`, the pair `{ν^y ρ, ν^(-y) ρ}`
completes a reflection-invariant family of one-element rectangles to another one. -/
theorem pair_identity {ρ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary) {y : ℝ} (hy : 0 < y) :
    ∃ L R : Multiset (RParam.{uF, uV} T), StFamily L ∧ StFamily R ∧
      pt ρ y ::ₘ pt ρ (-y) ::ₘ (L.map RParam.rect).sum = (R.map RParam.rect).sum := by
  by_cases h : ∃ m : ℕ, 2 * y = m + 1
  · obtain ⟨m, hm⟩ := h
    have hy' : y = ((m : ℝ) + 1) / 2 := by linarith
    have key := stParam_rect_succ_succ ρ m
    rw [← hy'] at key
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · refine ⟨0, {stParam ρ 2 0}, StFamily.zero, StFamily.single hρ (by norm_num), ?_⟩
      rw [Multiset.map_singleton, Multiset.sum_singleton, key, stParam_rect_zero]
      rfl
    · refine ⟨{stParam ρ m 0}, {stParam ρ (m + 2) 0}, StFamily.single hρ hm0,
        StFamily.single hρ (by omega), ?_⟩
      rw [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_singleton,
        Multiset.sum_singleton, key]
  · set m := ⌊2 * y⌋₊ with hmdef
    have hm1 : (m : ℝ) ≤ 2 * y := Nat.floor_le (by linarith)
    have hm2 : 2 * y < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hm3 : (m : ℝ) < 2 * y := by
      rcases lt_or_eq_of_le hm1 with h1 | h1
      · exact h1
      · exfalso
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at h1; push_cast at h1; linarith
        · exact h ⟨m - 1, by rw [← h1, Nat.cast_sub h0]; push_cast; ring⟩
    set α := y - (m : ℝ) / 2 with hαdef
    have hα0 : 0 < α := by linarith
    have hα1 : α < 1 / 2 := by linarith
    have hαabs : |α| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have ktop := stParam_rect_succ_top ρ m α
    have kbot := stParam_rect_succ_bot ρ m α
    have hya : α + (m : ℝ) / 2 = y := by rw [hαdef]; ring
    rw [hya] at ktop kbot
    rcases Nat.eq_zero_or_pos m with h0 | hm0
    · refine ⟨0, {stParam ρ (m + 1) α, stParam ρ (m + 1) (-α)}, StFamily.zero,
        StFamily.pair hρ (by omega) hαabs, ?_⟩
      rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton, ktop, kbot, h0, stParam_rect_zero,
        stParam_rect_zero, Multiset.map_zero, Multiset.sum_zero, Multiset.cons_add,
        Multiset.zero_add]
    · have hβ : |α - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
      refine ⟨{stParam ρ m (α - 1 / 2), stParam ρ m (-(α - 1 / 2))},
        {stParam ρ (m + 1) α, stParam ρ (m + 1) (-α)}, StFamily.pair hρ hm0 hβ,
        StFamily.pair hρ (by omega) hαabs, ?_⟩
      have e : -(α - 1 / 2) = 1 / 2 - α := by ring
      rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton, ktop, kbot, e]
      simp only [Multiset.cons_add, Multiset.add_cons]
      rw [Multiset.cons_swap]

/-- **One-element segments.** A reflection-invariant multisegment of unitary-based
one-element segments, completed by a reflection-invariant family of one-element rectangles,
becomes another such family. -/
theorem onePoint_decomposition : ∀ (k : ℕ) (φ : T.Multisegment.{max uF uV, uF}),
    Multiset.card φ = k → (∀ Δ ∈ φ, Δ.length = 1) → φ.map reflSeg = φ →
      ∃ L R : Multiset (RParam.{uF, max uF uV} T), StFamily L ∧ StFamily R ∧
        φ + (L.map RParam.rect).sum = (R.map RParam.rect).sum := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro φ hk hlen hrefl
  by_cases hφ : φ = 0
  · subst hφ
    exact ⟨0, 0, StFamily.zero, StFamily.zero, by simp⟩
  obtain ⟨Δ, hΔ⟩ := Multiset.exists_mem_of_ne_zero hφ
  obtain ⟨ρ, x, hρ, hb⟩ := unitaryBased Δ
  have hΔpt : Δ = pt ρ x := by
    obtain ⟨b, l, hl⟩ := Δ
    simp only at hb
    have hl1 : l = 1 := hlen _ hΔ
    subst hb hl1
    simp [tadicCenteredSegment]
  have hrefl_pt : ∀ z : ℝ, reflSeg (pt ρ z) = pt ρ (-z) := fun z =>
    reflSeg_tadicCenteredSegment hρ 1 Nat.one_pos z
  obtain ⟨φ₁, rfl⟩ := Multiset.exists_cons_of_mem hΔ
  by_cases hx : x = 0
  · -- a unitary one-element segment
    have hrefl₁ : φ₁.map reflSeg = φ₁ := by
      rw [Multiset.map_cons, hΔpt, hrefl_pt, hx, neg_zero] at hrefl
      exact (Multiset.cons_inj_right _).mp hrefl
    obtain ⟨L, R, hL, hR, hLR⟩ := ih (Multiset.card φ₁) (by rw [← hk, Multiset.card_cons]; omega)
      φ₁ rfl (fun Δ' h => hlen Δ' (Multiset.mem_cons_of_mem h)) hrefl₁
    refine ⟨L, stParam ρ 1 0 ::ₘ R, hL, ?_, ?_⟩
    · have := (StFamily.single (T := T) hρ Nat.one_pos).add hR
      rwa [Multiset.singleton_add] at this
    · rw [Multiset.map_cons, Multiset.sum_cons, stParam_rect_one, ← hLR, hΔpt, hx,
        Multiset.cons_add, Multiset.singleton_add]
  · -- a pair `{ν^x ρ, ν^(-x) ρ}`
    have hne : pt ρ (-x) ≠ pt ρ x := by
      intro h
      obtain ⟨-, -, h'⟩ := (tadicCenteredSegment_eq_iff hρ hρ).mp h
      exact hx (by linarith)
    have hmem : pt ρ (-x) ∈ φ₁ := by
      have hc : (Δ ::ₘ φ₁).count (pt ρ (-x)) = (Δ ::ₘ φ₁).count Δ := by
        conv_lhs => rw [← hrefl]
        rw [count_map_reflSeg, hrefl_pt, neg_neg, hΔpt]
      have hpos : 0 < (Δ ::ₘ φ₁).count Δ := Multiset.count_pos.mpr (Multiset.mem_cons_self _ _)
      rw [← hc, hΔpt] at hpos
      rcases Multiset.mem_cons.mp (Multiset.count_pos.mp hpos) with h | h
      · exact absurd h hne
      · exact h
    obtain ⟨φ₂, rfl⟩ := Multiset.exists_cons_of_mem hmem
    have hrefl₂ : φ₂.map reflSeg = φ₂ := by
      rw [Multiset.map_cons, Multiset.map_cons, hΔpt, hrefl_pt, hrefl_pt, neg_neg,
        Multiset.cons_swap] at hrefl
      exact (Multiset.cons_inj_right _).mp ((Multiset.cons_inj_right _).mp hrefl)
    obtain ⟨L₂, R₂, hL₂, hR₂, hLR₂⟩ := ih (Multiset.card φ₂)
      (by rw [← hk, Multiset.card_cons, Multiset.card_cons]; omega) φ₂ rfl
      (fun Δ' h => hlen Δ' (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem h))) hrefl₂
    have hy : 0 < |x| := abs_pos.mpr hx
    obtain ⟨L₁, R₁, hL₁, hR₁, hLR₁⟩ := pair_identity (T := T) hρ hy
    refine ⟨L₁ + L₂, R₁ + R₂, hL₁.add hL₂, hR₁.add hR₂, ?_⟩
    have hpair : pt ρ x ::ₘ pt ρ (-x) ::ₘ (0 : T.Multisegment.{max uF uV, uF}) =
        pt ρ |x| ::ₘ pt ρ (-|x|) ::ₘ 0 := by
      rcases abs_cases x with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
      · rw [h1, neg_neg, Multiset.cons_swap]
    rw [Multiset.map_add, Multiset.sum_add, Multiset.map_add, Multiset.sum_add, ← hLR₂, ← hLR₁,
      hΔpt]
    have e1 : pt ρ x ::ₘ pt ρ (-x) ::ₘ φ₂ = (pt ρ x ::ₘ pt ρ (-x) ::ₘ 0) + φ₂ := by simp
    have e2 : pt ρ |x| ::ₘ pt ρ (-|x|) ::ₘ (L₁.map RParam.rect).sum =
        (pt ρ |x| ::ₘ pt ρ (-|x|) ::ₘ 0) + (L₁.map RParam.rect).sum := by simp
    rw [e1, e2, hpair]
    abel

end Langlands.Classification.TadicBlockCombinatorics
