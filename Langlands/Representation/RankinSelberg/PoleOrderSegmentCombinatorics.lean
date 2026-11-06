import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentIntegralCoordinates
import Mathlib.Tactic

/-!
# Pole-test combinatorics of multisegments

The combinatorial core of Henniart 2002, §§4.2–4.4 (printed pages 599-600). A
segment on a line is an integral interval `[b, e]`; a test is an integral interval
`[g, h]` on a line, and the segment `[b, e]` is linked to the test exactly when
they lie on the same line and `b ≤ g ≤ e ≤ h`. The main abstract result,
`eq_of_testCount_eq`, recovers a multiset of segments of total degree `N`, other
than a single segment of length one, from its numbers of linked segments on the
tests of degree below `N`.

The last section transports this to the Library's segments of cuspidal data. A
segment `Δ` is linked to a segment `D` when `D` begins in `Δ` and `Δ` ends in `D`
(`SegmentPoleLink`), and `multisegment_eq_of_poleLinkCount_eq` is the recovery
theorem for multisegments. No statement about L-factors is made here.
-/

noncomputable section

namespace Langlands.RankinSelberg

universe u

/-- An abstract segment: the integral interval `[lower, lower + length - 1]`,
`length ≥ 1`, on the line `line`. -/
@[ext]
structure IntervalSegment (ι : Type u) where
  /-- The line carrying the segment. -/
  line : ι
  /-- The lower endpoint `b`. -/
  lower : ℤ
  /-- The number of points of the segment. -/
  length : ℕ
  length_pos : 0 < length

namespace IntervalSegment

variable {ι : Type u}

/-- The upper endpoint `e = b + length - 1`. -/
def upper (Δ : IntervalSegment ι) : ℤ := Δ.lower + Δ.length - 1

theorem lower_le_upper (Δ : IntervalSegment ι) : Δ.lower ≤ Δ.upper := by
  have := Δ.length_pos
  unfold upper
  omega

/-- The segment `Δ = [b, e]` contributes to the test interval `[g, g + k - 1]` on the
line `c`: `Δ` lies on `c` and `b ≤ g ≤ e ≤ g + k - 1`. -/
def LinksTo (Δ : IntervalSegment ι) (c : ι) (g : ℤ) (k : ℕ) : Prop :=
  Δ.line = c ∧ Δ.lower ≤ g ∧ g ≤ Δ.upper ∧ Δ.upper < g + k

/-- The degree `length · w(line)` of a segment for line weights `w`. -/
def degree (w : ι → ℕ) (Δ : IntervalSegment ι) : ℕ := Δ.length * w Δ.line

theorem degree_pos {w : ι → ℕ} (hw : ∀ c, 0 < w c) (Δ : IntervalSegment ι) :
    0 < Δ.degree w :=
  Nat.mul_pos Δ.length_pos (hw Δ.line)

end IntervalSegment

open IntervalSegment

variable {ι : Type u}

open Classical

/-- The number of segments of `a`, with multiplicity, contributing to the test
interval `[g, g + k - 1]` on the line `c`. -/
def rawTestCount (a : Multiset (IntervalSegment ι)) (c : ι) (g : ℤ) (k : ℕ) : ℕ :=
  a.countP (fun Δ => Δ.LinksTo c g k)

/-- The number of segments of `a` contributing to the test segment `D`. -/
def testCount (a : Multiset (IntervalSegment ι)) (D : IntervalSegment ι) : ℕ :=
  rawTestCount a D.line D.lower D.length

/-- The total degree of a multiset of segments. -/
def multisetDegree (w : ι → ℕ) (a : Multiset (IntervalSegment ι)) : ℕ :=
  (a.map (IntervalSegment.degree w)).sum

section Lemmas

variable (w : ι → ℕ)

theorem multisetDegree_zero : multisetDegree w (0 : Multiset (IntervalSegment ι)) = 0 := by
  simp [multisetDegree]

theorem multisetDegree_add (a b : Multiset (IntervalSegment ι)) :
    multisetDegree w (a + b) = multisetDegree w a + multisetDegree w b := by
  simp [multisetDegree]

theorem multisetDegree_cons (Δ : IntervalSegment ι) (a : Multiset (IntervalSegment ι)) :
    multisetDegree w (Δ ::ₘ a) = Δ.degree w + multisetDegree w a := by
  simp [multisetDegree]

theorem multisetDegree_singleton (Δ : IntervalSegment ι) :
    multisetDegree w {Δ} = Δ.degree w := by
  simp [multisetDegree]

variable {w}

theorem multisetDegree_eq_zero_iff (hw : ∀ c, 0 < w c) {a : Multiset (IntervalSegment ι)} :
    multisetDegree w a = 0 ↔ a = 0 := by
  constructor
  · intro h
    induction a using Multiset.induction_on with
    | empty => rfl
    | cons Δ a _ =>
      rw [multisetDegree_cons] at h
      have := Δ.degree_pos hw
      omega
  · rintro rfl
    exact multisetDegree_zero w

theorem degree_le_multisetDegree {a : Multiset (IntervalSegment ι)} {Δ : IntervalSegment ι}
    (h : Δ ∈ a) : Δ.degree w ≤ multisetDegree w a := by
  rw [← Multiset.cons_erase h, multisetDegree_cons]
  omega

theorem eq_singleton_of_degree_eq (hw : ∀ c, 0 < w c) {a : Multiset (IntervalSegment ι)}
    {Δ : IntervalSegment ι} (h : Δ ∈ a) (hd : multisetDegree w a ≤ Δ.degree w) : a = {Δ} := by
  rw [← Multiset.cons_erase h] at hd ⊢
  rw [multisetDegree_cons] at hd
  have : multisetDegree w (a.erase Δ) = 0 := by omega
  rw [(multisetDegree_eq_zero_iff hw).mp this]
  rfl

theorem card_mul_le_two_mul_multisetDegree {N : ℕ} {a : Multiset (IntervalSegment ι)}
    (h : ∀ Δ ∈ a, N ≤ 2 * Δ.degree w) : Multiset.card a * N ≤ 2 * multisetDegree w a := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons Δ a ih =>
    rw [Multiset.card_cons, multisetDegree_cons]
    have h1 := h Δ (Multiset.mem_cons_self Δ a)
    have h2 := ih fun Γ hΓ => h Γ (Multiset.mem_cons_of_mem hΓ)
    rw [Nat.succ_mul]
    omega

theorem rawTestCount_add (a b : Multiset (IntervalSegment ι)) (c : ι) (g : ℤ) (k : ℕ) :
    rawTestCount (a + b) c g k = rawTestCount a c g k + rawTestCount b c g k := by
  simp only [rawTestCount, Multiset.countP_add]

theorem rawTestCount_zero_length (a : Multiset (IntervalSegment ι)) (c : ι) (g : ℤ) :
    rawTestCount a c g 0 = 0 := by
  simp only [rawTestCount, Multiset.countP_eq_zero]
  rintro Δ - ⟨-, h1, h2, h3⟩
  push_cast at h3
  omega

/-- The indicator of a single segment is an alternating sum of four test
contributions (Henniart 2002, §4.2, formulas (1)–(2) and the display after them). -/
theorem indicator_eq_alternating (Δ Δ₀ : IntervalSegment ι) :
    ((if Δ = Δ₀ then 1 else 0 : ℕ) : ℤ) =
      ((if Δ.LinksTo Δ₀.line Δ₀.lower Δ₀.length then 1 else 0 : ℕ) : ℤ) -
        ((if Δ.LinksTo Δ₀.line Δ₀.lower (Δ₀.length - 1) then 1 else 0 : ℕ) : ℤ) -
        ((if Δ.LinksTo Δ₀.line (Δ₀.lower - 1) (Δ₀.length + 1) then 1 else 0 : ℕ) : ℤ) +
        ((if Δ.LinksTo Δ₀.line (Δ₀.lower - 1) Δ₀.length then 1 else 0 : ℕ) : ℤ) := by
  have h₀ := Δ₀.length_pos
  have h := Δ.length_pos
  by_cases hl : Δ.line = Δ₀.line
  · have hiff : Δ = Δ₀ ↔ Δ.lower = Δ₀.lower ∧ Δ.length = Δ₀.length := by
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        exact IntervalSegment.ext hl h1 h2
    simp only [LinksTo, upper, hl, true_and, hiff]
    split_ifs <;> push_cast at * <;> omega
  · have hne : Δ ≠ Δ₀ := fun h => hl (h ▸ rfl)
    simp [LinksTo, hl, hne]

/-- Multiplicities are alternating sums of test counts (Henniart 2002, §4.2). -/
theorem count_eq_alternating (a : Multiset (IntervalSegment ι))
    (Δ₀ : IntervalSegment ι) :
    (a.count Δ₀ : ℤ) =
      (rawTestCount a Δ₀.line Δ₀.lower Δ₀.length : ℤ) -
        rawTestCount a Δ₀.line Δ₀.lower (Δ₀.length - 1) -
        rawTestCount a Δ₀.line (Δ₀.lower - 1) (Δ₀.length + 1) +
        rawTestCount a Δ₀.line (Δ₀.lower - 1) Δ₀.length := by
  induction a using Multiset.induction_on with
  | empty => simp [rawTestCount]
  | cons Δ a ih =>
    have key := indicator_eq_alternating Δ Δ₀
    simp only [rawTestCount] at ih ⊢
    rw [Multiset.count_cons, Multiset.countP_cons, Multiset.countP_cons,
      Multiset.countP_cons, Multiset.countP_cons]
    have e : (if Δ₀ = Δ then 1 else 0 : ℕ) = (if Δ = Δ₀ then 1 else 0 : ℕ) := by
      by_cases h : Δ = Δ₀
      · simp [h]
      · simp [h, Ne.symm h]
    rw [e]
    push_cast at ih key ⊢
    linarith

end Lemmas

section Recovery

variable {w : ι → ℕ}

/-- The end point `(line, upper)` of a segment. -/
def IntervalSegment.endPoint (Δ : IntervalSegment ι) : ι × ℤ := (Δ.line, Δ.upper)

/-- The segment of length one at a point. -/
def IntervalSegment.point (p : ι × ℤ) : IntervalSegment ι := ⟨p.1, p.2, 1, Nat.one_pos⟩

theorem IntervalSegment.point_endPoint {Δ : IntervalSegment ι} (h : Δ.length = 1) :
    IntervalSegment.point Δ.endPoint = Δ := by
  ext
  · rfl
  · simp [point, endPoint, upper, h]
  · simp [point, h]

/-- Tests of length one count end points. -/
theorem rawTestCount_one (a : Multiset (IntervalSegment ι)) (c : ι) (x : ℤ) :
    rawTestCount a c x 1 = (a.map IntervalSegment.endPoint).count (c, x) := by
  rw [Multiset.count_map, ← Multiset.countP_eq_card_filter, rawTestCount]
  refine Multiset.countP_congr rfl fun Δ _ => ?_
  have := Δ.lower_le_upper
  simp only [LinksTo, endPoint, Prod.ext_iff, eq_iff_iff]
  push_cast
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    exact ⟨h1.symm, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, by omega, by omega, by omega⟩

/-- Test counts on segments of degree below `N` give the counts on all intervals of
degree below `N`. -/
theorem rawTestCount_eq_of_testCount_eq {N : ℕ} {a a' : Multiset (IntervalSegment ι)}
    (htest : ∀ D : IntervalSegment ι, D.degree w < N → testCount a D = testCount a' D)
    (c : ι) (g : ℤ) (k : ℕ) (hk : k * w c < N) :
    rawTestCount a c g k = rawTestCount a' c g k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [rawTestCount_zero_length, rawTestCount_zero_length]
  · exact htest ⟨c, g, k, hk0⟩ hk

/-- A segment whose doubled length times its weight is below `N` has the same
multiplicity in two multisets with the same counts on intervals of degree below
`N` (Henniart 2002, §4.2). -/
theorem count_eq_of_rawTestCount_eq {N : ℕ} {b b' : Multiset (IntervalSegment ι)}
    (hraw : ∀ c g k, k * w c < N → rawTestCount b c g k = rawTestCount b' c g k)
    (Δ : IntervalSegment ι) (hΔ : (Δ.length + 1) * w Δ.line < N) :
    b.count Δ = b'.count Δ := by
  have h1 : Δ.length * w Δ.line < N :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ _)) hΔ
  have h2 : (Δ.length - 1) * w Δ.line < N :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) h1
  have e := count_eq_alternating b Δ
  have e' := count_eq_alternating b' Δ
  rw [hraw _ _ _ h1, hraw _ _ _ h2, hraw _ _ _ hΔ, hraw _ _ _ h1] at e
  exact_mod_cast e.trans e'.symm

/-- The core recovery step. Two multisets of segments with no common element, the
same total degree at most `N`, all lines of weight below `N`, and the same counts
on intervals of degree below `N` are equal. -/
theorem eq_of_rawTestCount_eq_of_disjoint (hw : ∀ c, 0 < w c) {N : ℕ}
    {b b' : Multiset (IntervalSegment ι)} (hdisj : ∀ Δ ∈ b, Δ ∉ b')
    (hdeg : multisetDegree w b = multisetDegree w b') (hN : multisetDegree w b ≤ N)
    (hvalid : ∀ Δ ∈ b, w Δ.line < N) (hvalid' : ∀ Δ ∈ b', w Δ.line < N)
    (hraw : ∀ c g k, k * w c < N → rawTestCount b c g k = rawTestCount b' c g k) :
    b = b' := by
  -- Every segment of `b` or `b'` has `N ≤ (length + 1) · w(line)`.
  have long : ∀ Δ ∈ b, N ≤ (Δ.length + 1) * w Δ.line := by
    intro Δ hΔ
    by_contra hlt
    have hc := count_eq_of_rawTestCount_eq hraw Δ (Nat.lt_of_not_le hlt)
    have : 0 < b'.count Δ := hc ▸ Multiset.count_pos.mpr hΔ
    exact hdisj Δ hΔ (Multiset.count_pos.mp this)
  have long' : ∀ Δ ∈ b', N ≤ (Δ.length + 1) * w Δ.line := by
    intro Δ hΔ
    by_contra hlt
    have hc := count_eq_of_rawTestCount_eq hraw Δ (Nat.lt_of_not_le hlt)
    have : 0 < b.count Δ := hc ▸ Multiset.count_pos.mpr hΔ
    exact hdisj Δ (Multiset.count_pos.mp this) hΔ
  have twice : ∀ Δ : IntervalSegment ι, N ≤ (Δ.length + 1) * w Δ.line →
      N ≤ 2 * Δ.degree w := by
    intro Δ h
    have := Δ.length_pos
    have : (Δ.length + 1) * w Δ.line ≤ (2 * Δ.length) * w Δ.line :=
      Nat.mul_le_mul_right _ (by omega)
    unfold IntervalSegment.degree
    rw [← Nat.mul_assoc]
    omega
  -- The end points agree.
  have hend : b.map IntervalSegment.endPoint = b'.map IntervalSegment.endPoint := by
    ext ⟨c, x⟩
    by_cases hc : w c < N
    · rw [← rawTestCount_one, ← rawTestCount_one]
      exact hraw c x 1 (by omega)
    · have z : ∀ m : Multiset (IntervalSegment ι), (∀ Δ ∈ m, w Δ.line < N) →
          (m.map IntervalSegment.endPoint).count (c, x) = 0 := by
        intro m hm
        rw [Multiset.count_eq_zero, Multiset.mem_map]
        rintro ⟨Δ, hΔ, he⟩
        have := hm Δ hΔ
        simp only [IntervalSegment.endPoint, Prod.mk.injEq] at he
        rw [he.1] at this
        exact hc this
      rw [z b hvalid, z b' hvalid']
  have hcard : Multiset.card b = Multiset.card b' := by
    rw [← Multiset.card_map IntervalSegment.endPoint b, hend, Multiset.card_map]
  -- Segments of length one are determined by their end points.
  have of_lengths : (∀ Δ ∈ b, Δ.length = 1) → (∀ Δ ∈ b', Δ.length = 1) → b = b' := by
    intro h h'
    have key : ∀ m : Multiset (IntervalSegment ι), (∀ Δ ∈ m, Δ.length = 1) →
        (m.map IntervalSegment.endPoint).map IntervalSegment.point = m := by
      intro m hm
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id m]
      exact Multiset.map_congr rfl fun Δ hΔ => IntervalSegment.point_endPoint (hm Δ hΔ)
    rw [← key b h, ← key b' h', hend]
  -- Lengths are one when there are two segments.
  have two : ∀ m : Multiset (IntervalSegment ι), Multiset.card m = 2 →
      multisetDegree w m ≤ N → (∀ Δ ∈ m, N ≤ (Δ.length + 1) * w Δ.line) →
      ∀ Δ ∈ m, Δ.length = 1 := by
    intro m hm hmN hml
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp hm
    have hx := hml x (by simp)
    have hy := hml y (by simp)
    have hx2 := twice x hx
    have hy2 := twice y hy
    have hsum : x.degree w + y.degree w ≤ N := by
      simpa [multisetDegree] using hmN
    have one : ∀ Δ : IntervalSegment ι, N ≤ (Δ.length + 1) * w Δ.line →
        2 * Δ.degree w ≤ N → Δ.length = 1 := by
      intro Δ h1 h2
      have := Δ.length_pos
      have hwΔ := hw Δ.line
      unfold IntervalSegment.degree at h2
      have : Δ.length * w Δ.line ≤ 1 * w Δ.line := by
        rw [Nat.add_mul] at h1
        omega
      have := Nat.le_of_mul_le_mul_right this hwΔ
      omega
    intro Δ hΔ
    rcases Multiset.mem_cons.mp hΔ with rfl | hΔ
    · exact one _ hx (by omega)
    · rw [Multiset.mem_singleton.mp hΔ]
      exact one _ hy (by omega)
  -- Conclude by the number of segments.
  have hcardN : Multiset.card b * N ≤ 2 * multisetDegree w b :=
    card_mul_le_two_mul_multisetDegree fun Δ hΔ => twice Δ (long Δ hΔ)
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · have e : ∀ m : Multiset (IntervalSegment ι), (∀ Δ ∈ m, w Δ.line < N) → m = 0 := by
      intro m hm
      refine Multiset.eq_zero_of_forall_notMem fun Δ hΔ => ?_
      have := hm Δ hΔ
      omega
    rw [e b hvalid, e b' hvalid']
  have hcard2 : Multiset.card b ≤ 2 := by
    by_contra h
    have : 3 * N ≤ Multiset.card b * N := Nat.mul_le_mul_right _ (by omega)
    omega
  interval_cases hb : Multiset.card b
  · rw [Multiset.card_eq_zero.mp hb, Multiset.card_eq_zero.mp hcard.symm]
  · obtain ⟨Δ, rfl⟩ := Multiset.card_eq_one.mp hb
    obtain ⟨Δ', rfl⟩ := Multiset.card_eq_one.mp hcard.symm
    simp only [Multiset.map_singleton, Multiset.singleton_inj, IntervalSegment.endPoint,
      Prod.mk.injEq] at hend
    rw [multisetDegree_singleton, multisetDegree_singleton] at hdeg
    unfold IntervalSegment.degree at hdeg
    rw [hend.1] at hdeg
    have hl : Δ.length = Δ'.length := Nat.eq_of_mul_eq_mul_right (hw _) hdeg
    have hu := hend.2
    unfold IntervalSegment.upper at hu
    rw [hl] at hu
    rw [IntervalSegment.ext hend.1 (by omega) hl]
  · have hbN : multisetDegree w b = N := by omega
    exact of_lengths (two b hb (by omega) long) (two b' hcard.symm (by omega) long')

/-- A segment of weight at least `N` in a multiset of total degree `N` is all of
it, and has length one. -/
theorem eq_singleton_of_le_weight (hw : ∀ c, 0 < w c) {N : ℕ}
    {a : Multiset (IntervalSegment ι)} (ha : multisetDegree w a = N) {Δ : IntervalSegment ι}
    (hΔ : Δ ∈ a) (hN : N ≤ w Δ.line) : a = {Δ} ∧ Δ.length = 1 := by
  have hle := degree_le_multisetDegree (w := w) hΔ
  have hlen := Δ.length_pos
  unfold IntervalSegment.degree at hle
  refine ⟨eq_singleton_of_degree_eq hw hΔ ?_, ?_⟩
  · unfold IntervalSegment.degree
    rw [ha]
    exact le_trans hN (Nat.le_mul_of_pos_left _ hlen)
  · by_contra h
    have : 2 * w Δ.line ≤ Δ.length * w Δ.line := Nat.mul_le_mul_right _ (by omega)
    have := hw Δ.line
    omega

/-- **Recovery of multisegments from pole counts** (Henniart 2002, §§4.2–4.4). Let
`a` and `a'` be multisets of segments of total degree `N`, `a` not a single segment
of length one. If they have the same counts on every test segment of degree below
`N`, then `a = a'`. -/
theorem eq_of_testCount_eq (hw : ∀ c, 0 < w c) {N : ℕ}
    {a a' : Multiset (IntervalSegment ι)} (ha : multisetDegree w a = N)
    (ha' : multisetDegree w a' = N) (hns : ∀ Δ : IntervalSegment ι, Δ.length = 1 → a ≠ {Δ})
    (htest : ∀ D : IntervalSegment ι, D.degree w < N → testCount a D = testCount a' D) :
    a = a' := by
  have hraw := rawTestCount_eq_of_testCount_eq htest
  -- Every line of `a` has weight below `N`.
  have hvalid : ∀ Δ ∈ a, w Δ.line < N := by
    intro Δ hΔ
    by_contra h
    obtain ⟨h1, h2⟩ := eq_singleton_of_le_weight hw ha hΔ (Nat.le_of_not_lt h)
    exact hns Δ h2 h1
  -- Every line of `a'` has weight below `N`.
  have hvalid' : ∀ Δ ∈ a', w Δ.line < N := by
    intro Δ' hΔ'
    by_contra h
    obtain ⟨h1, -⟩ := eq_singleton_of_le_weight hw ha' hΔ' (Nat.le_of_not_lt h)
    obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ ∈ a := by
      by_contra hne
      have : a = 0 := Multiset.eq_zero_of_forall_notMem fun Δ hΔ => hne ⟨Δ, hΔ⟩
      rw [this, multisetDegree_zero] at ha
      rw [h1, multisetDegree_singleton, ← ha] at ha'
      exact (Δ'.degree_pos hw).ne' ha'
    have e := hraw Δ.line Δ.upper 1 (by simpa using hvalid Δ hΔ)
    rw [rawTestCount_one, rawTestCount_one, h1, Multiset.map_singleton,
      Multiset.count_singleton] at e
    have hpos : 0 < (a.map IntervalSegment.endPoint).count (Δ.line, Δ.upper) :=
      Multiset.count_pos.mpr (Multiset.mem_map_of_mem _ hΔ)
    rw [e] at hpos
    split_ifs at hpos with heq
    · simp only [IntervalSegment.endPoint, Prod.mk.injEq] at heq
      have := hvalid Δ hΔ
      rw [heq.1] at this
      exact h this
    · exact Nat.lt_irrefl 0 hpos
  -- Remove the common part.
  set s := a ∩ a' with hs
  have hsa : s ≤ a := Multiset.inter_le_left
  have hsa' : s ≤ a' := Multiset.inter_le_right
  have eb : a = s + (a - s) := (add_tsub_cancel_of_le hsa).symm
  have eb' : a' = s + (a' - s) := (add_tsub_cancel_of_le hsa').symm
  suffices h : a - s = a' - s by rw [eb, eb', h]
  have hdeg := ha.trans ha'.symm
  rw [eb, eb', multisetDegree_add, multisetDegree_add] at hdeg
  refine eq_of_rawTestCount_eq_of_disjoint hw (N := N) ?_ (by omega) ?_ ?_ ?_ ?_
  · intro Δ hΔ hΔ'
    rw [← Multiset.count_pos, Multiset.count_sub, hs, Multiset.count_inter] at hΔ hΔ'
    omega
  · have := ha
    rw [eb, multisetDegree_add] at this
    omega
  · exact fun Δ hΔ => hvalid Δ (Multiset.mem_of_le tsub_le_self hΔ)
  · exact fun Δ hΔ => hvalid' Δ (Multiset.mem_of_le tsub_le_self hΔ)
  · intro c g k hk
    have e := hraw c g k hk
    rw [eb, eb', rawTestCount_add, rawTestCount_add] at e
    omega

end Recovery

section Segments

/-! ### Segments of cuspidal data

The Library's segments `[ρ, ν^(m-1) ρ]` of cuspidal data receive integral
coordinates: the line of `ρ` is its class modulo integral twists, its position is
its exponent relative to a chosen representative of the line, and the weight of a
line is the common rank of its data. Integral twist freeness, proved in the
Library, makes positions unique. -/

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The relation `σ = ν^k ρ` for an integer `k`. -/
def integralTwistSetoid (T : F.TopologicalData) : Setoid (CuspidalDatum.{uV, uF} T) where
  r σ ρ := ∃ k : ℤ, σ = ρ.twist (k : ℝ)
  iseqv :=
    { refl := fun ρ => ⟨0, by simp⟩
      symm := by
        rintro σ ρ ⟨k, rfl⟩
        exact ⟨-k, by simp [CuspidalDatum.twist_twist]⟩
      trans := by
        rintro σ ρ τ ⟨k, rfl⟩ ⟨l, rfl⟩
        exact ⟨k + l, by rw [CuspidalDatum.twist_twist, Int.cast_add]⟩ }

/-- The integral twist lines `{ν^k ρ : k ∈ ℤ}` of cuspidal data. -/
abbrev IntegralTwistLine (T : F.TopologicalData) := Quotient (integralTwistSetoid.{uF, uV} T)

/-- The integral twist line of a cuspidal datum. -/
def twistLine (σ : CuspidalDatum.{uV, uF} T) : IntegralTwistLine.{uF, uV} T :=
  Quotient.mk _ σ

theorem exists_eq_twist_out (σ : CuspidalDatum.{uV, uF} T) :
    ∃ k : ℤ, σ = (twistLine σ).out.twist (k : ℝ) := by
  obtain ⟨k, hk⟩ := Quotient.mk_out (s := integralTwistSetoid.{uF, uV} T) σ
  refine ⟨-k, ?_⟩
  change σ = (Quotient.mk _ σ : IntegralTwistLine.{uF, uV} T).out.twist _
  rw [hk, CuspidalDatum.twist_twist]
  simp

/-- The position `k` of `σ = ν^k ρ₀` on its line, `ρ₀` the chosen representative
of the line. -/
def twistPosition (σ : CuspidalDatum.{uV, uF} T) : ℤ :=
  (exists_eq_twist_out σ).choose

theorem twistPosition_spec (σ : CuspidalDatum.{uV, uF} T) :
    σ = (twistLine σ).out.twist (twistPosition σ : ℝ) :=
  (exists_eq_twist_out σ).choose_spec

theorem twistLine_twist (σ : CuspidalDatum.{uV, uF} T) (k : ℤ) :
    twistLine (σ.twist (k : ℝ)) = twistLine σ :=
  Quotient.sound ⟨k, rfl⟩

theorem twistLine_out_twist (c : IntegralTwistLine.{uF, uV} T) (k : ℤ) :
    twistLine (c.out.twist (k : ℝ)) = c := by
  rw [twistLine_twist]
  exact Quotient.out_eq c

theorem twistPosition_out_twist (c : IntegralTwistLine.{uF, uV} T) (k : ℤ) :
    twistPosition (c.out.twist (k : ℝ)) = k := by
  have h := twistPosition_spec (c.out.twist (k : ℝ))
  rw [twistLine_out_twist] at h
  exact c.out.integralTwist_injective (Classification.cuspidalIntegralTwistFreeness F T) h.symm

theorem twistLine_of_mem_support {Δ : Segment.{uV, uF} T} {σ : CuspidalDatum.{uV, uF} T}
    (h : σ ∈ Δ.support) : twistLine σ = twistLine Δ.base := by
  obtain ⟨i, -, rfl⟩ := h
  have : Δ.member i = Δ.base.twist ((i : ℤ) : ℝ) := by simp [Segment.member]
  rw [this, twistLine_twist]

/-- The weight of a line: the common rank of its cuspidal data. -/
def lineWeight (c : IntegralTwistLine.{uF, uV} T) : ℕ := c.out.rank

theorem lineWeight_pos (c : IntegralTwistLine.{uF, uV} T) : 0 < lineWeight c :=
  c.out.rank_pos

theorem rank_eq_lineWeight (σ : CuspidalDatum.{uV, uF} T) :
    σ.rank = lineWeight (twistLine σ) := by
  have h := congrArg CuspidalDatum.rank (twistPosition_spec σ)
  rw [CuspidalDatum.twist_rank] at h
  exact h

/-- The integral coordinates of a segment. -/
def segmentCoordinates (Δ : Segment.{uV, uF} T) : IntervalSegment (IntegralTwistLine.{uF, uV} T) :=
  ⟨twistLine Δ.base, twistPosition Δ.base, Δ.length, Δ.length_pos⟩

/-- The segment with given integral coordinates. -/
def segmentOfCoordinates (D : IntervalSegment (IntegralTwistLine.{uF, uV} T)) :
    Segment.{uV, uF} T :=
  ⟨D.line.out.twist (D.lower : ℝ), D.length, D.length_pos⟩

theorem segmentCoordinates_segmentOfCoordinates
    (D : IntervalSegment (IntegralTwistLine.{uF, uV} T)) :
    segmentCoordinates (segmentOfCoordinates D) = D := by
  ext
  · exact twistLine_out_twist _ _
  · exact twistPosition_out_twist _ _
  · rfl

theorem segmentCoordinates_injective :
    Function.Injective (segmentCoordinates (T := T)) := by
  intro Δ Γ h
  have hl : twistLine Δ.base = twistLine Γ.base := congrArg IntervalSegment.line h
  have hp : twistPosition Δ.base = twistPosition Γ.base := congrArg IntervalSegment.lower h
  have hn : Δ.length = Γ.length := congrArg IntervalSegment.length h
  have hb : Δ.base = Γ.base :=
    calc Δ.base = (twistLine Δ.base).out.twist (twistPosition Δ.base : ℝ) :=
          twistPosition_spec _
      _ = (twistLine Γ.base).out.twist (twistPosition Γ.base : ℝ) := by rw [hl, hp]
      _ = Γ.base := (twistPosition_spec _).symm
  cases Δ
  cases Γ
  simp only at hb hn
  subst hb hn
  rfl

theorem degree_segmentCoordinates (Δ : Segment.{uV, uF} T) :
    (segmentCoordinates Δ).degree lineWeight = Δ.degree := by
  change Δ.length * lineWeight (twistLine Δ.base) = Δ.length * Δ.base.rank
  rw [rank_eq_lineWeight]

theorem hasIntegralCoordinates_segmentCoordinates (Δ : Segment.{uV, uF} T) :
    Δ.HasIntegralCoordinates (twistLine Δ.base).out (twistPosition Δ.base)
      (segmentCoordinates Δ).upper :=
  ⟨twistPosition_spec Δ.base, rfl⟩

theorem last_eq_twist_upper (Δ : Segment.{uV, uF} T) :
    Δ.last = (twistLine Δ.base).out.twist ((segmentCoordinates Δ).upper : ℝ) := by
  rw [Segment.last, (hasIntegralCoordinates_segmentCoordinates Δ).member_eq]
  have := Δ.length_pos
  have e : twistPosition Δ.base + ((Δ.length - 1 : ℕ) : ℤ) = (segmentCoordinates Δ).upper := by
    simp only [segmentCoordinates, IntervalSegment.upper]
    omega
  rw [e]

/-- The segment `D` begins in `Δ` and `Δ` ends in `D`. -/
def SegmentPoleLink (Δ D : Segment.{uV, uF} T) : Prop :=
  D.base ∈ Δ.support ∧ Δ.last ∈ D.support

theorem segmentPoleLink_iff (Δ D : Segment.{uV, uF} T) :
    SegmentPoleLink Δ D ↔ (segmentCoordinates Δ).LinksTo (segmentCoordinates D).line
      (segmentCoordinates D).lower (segmentCoordinates D).length := by
  have hfree := Classification.cuspidalIntegralTwistFreeness F T
  have hΔ := hasIntegralCoordinates_segmentCoordinates Δ
  have hD := hasIntegralCoordinates_segmentCoordinates D
  -- Both conditions put `D` on the line of `Δ`.
  suffices key : twistLine D.base = twistLine Δ.base →
      (SegmentPoleLink Δ D ↔ (segmentCoordinates Δ).LinksTo (segmentCoordinates D).line
        (segmentCoordinates D).lower (segmentCoordinates D).length) by
    constructor
    · intro h
      exact (key (twistLine_of_mem_support h.1)).mp h
    · intro h
      exact (key h.1.symm).mpr h
  intro hl
  rw [hl] at hD
  have hDbase : D.base = (twistLine Δ.base).out.twist (twistPosition D.base : ℝ) := hD.1
  rw [SegmentPoleLink, hDbase, last_eq_twist_upper, hΔ.twist_mem_support_iff hfree,
    hD.twist_mem_support_iff hfree]
  simp only [IntervalSegment.LinksTo, segmentCoordinates, IntervalSegment.upper, hl,
    true_and] at *
  omega

/-- The number of segments `Δ` of `a`, with multiplicity, such that `D` begins in
`Δ` and `Δ` ends in `D`. -/
def poleLinkCount (a : Multisegment.{uV, uF} T) (D : Segment.{uV, uF} T) : ℕ :=
  a.countP fun Δ => SegmentPoleLink Δ D

theorem poleLinkCount_eq_testCount (a : Multisegment.{uV, uF} T) (D : Segment.{uV, uF} T) :
    poleLinkCount a D = testCount (a.map segmentCoordinates) (segmentCoordinates D) := by
  rw [testCount, rawTestCount, Multiset.countP_map, ← Multiset.countP_eq_card_filter,
    poleLinkCount]
  exact Multiset.countP_congr rfl fun Δ _ => propext (segmentPoleLink_iff Δ D)

theorem multisetDegree_map_segmentCoordinates (a : Multisegment.{uV, uF} T) :
    multisetDegree lineWeight (a.map segmentCoordinates) = a.degree := by
  simp only [multisetDegree, Multisegment.degree, Multiset.map_map, Function.comp_def,
    degree_segmentCoordinates]

/-- **Henniart 2002, §§4.2–4.4, on multisegments.** Let `a` and `a'` be
multisegments of degree `N`, `a` not a single segment of length one. If, for every
segment `D` of degree below `N`, the numbers of segments `Δ` of `a` and of `a'`
such that `D` begins in `Δ` and `Δ` ends in `D` agree, then `a = a'`. -/
theorem multisegment_eq_of_poleLinkCount_eq {N : ℕ} {a a' : Multisegment.{uV, uF} T}
    (ha : a.degree = N) (ha' : a'.degree = N)
    (hns : ∀ Δ : Segment.{uV, uF} T, Δ.length = 1 → a ≠ {Δ})
    (htest : ∀ D : Segment.{uV, uF} T, D.degree < N → poleLinkCount a D = poleLinkCount a' D) :
    a = a' := by
  apply Multiset.map_injective segmentCoordinates_injective
  refine eq_of_testCount_eq (w := lineWeight) lineWeight_pos (N := N) ?_ ?_ ?_ ?_
  · rw [multisetDegree_map_segmentCoordinates, ha]
  · rw [multisetDegree_map_segmentCoordinates, ha']
  · intro Δ hΔ h
    obtain ⟨Γ, rfl, hΓ⟩ := Multiset.map_eq_singleton.mp h
    exact hns Γ (by rw [← hΓ] at hΔ; exact hΔ) rfl
  · intro D hD
    rw [← segmentCoordinates_segmentOfCoordinates D, ← poleLinkCount_eq_testCount,
      ← poleLinkCount_eq_testCount]
    apply htest
    rw [← degree_segmentCoordinates, segmentCoordinates_segmentOfCoordinates]
    exact hD

end Segments

end Langlands.RankinSelberg
