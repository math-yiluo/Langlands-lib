import Langlands.Representation.Classification.TadicSupportIdentification

/-!
# `a(d,n)^ρ` is not a sum of smaller Tadić pieces

Tadić's proof of Theorem A.10 needs that the multisegment `a(d,n)^ρ` (with `ρ`
unitary) is not the sum of multisegments each of which is either some
`a(v,u)^τ` of smaller degree with `τ` unitary, or a twist `ν^s a(v,u)^τ` with
`0 < |s| < 1/2`. A twisted piece would force `2s ∈ ℤ`; untwisted pieces are
`a(v,n)^ρ`, each containing exactly one segment centered at `0` or `1/2`, of which
`a(d,n)^ρ` has exactly one.
-/

noncomputable section

namespace Langlands.Classification

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A piece in the Langlands form of a product of Tadić blocks of degree at most `m`:
`a(u,v)^τ` itself, of degree at most `m`, or a twist `ν^s a(u,v)^τ` with
`0 < |s| < 1/2`, where `u, v > 0` and `τ` is unitary. -/
def IsTadicHeadPiece (m : ℕ) (c : T.Multisegment.{uV, uF}) : Prop :=
  ∃ (τ : T.CuspidalDatum.{uV, uF}) (u v : ℕ) (hv : 0 < v), 0 < u ∧ τ.IsUnitary ∧
    ((c = tadicMultisegment τ u v hv ∧ c.degree ≤ m) ∨
      ∃ s : ℝ, 0 < |s| ∧ |s| < 1 / 2 ∧ c = (tadicMultisegment τ u v hv).twist s)

theorem mem_tadicMultisegment {ρ : T.CuspidalDatum.{uV, uF}} {n d : ℕ} {hd : 0 < d}
    {Δ : T.Segment.{uV, uF}} :
    Δ ∈ tadicMultisegment ρ n d hd ↔
      ∃ j < n, tadicCenteredSegment ρ d hd ((j : ℝ) - ((n : ℝ) - 1) / 2) = Δ := by
  simp [tadicMultisegment]

/-- Matching a twisted centered segment with a centered segment of a unitary
cuspidal datum determines the datum, the length and the center. -/
theorem tadicCenteredSegment_twist_eq {ρ τ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary)
    (hτ : τ.IsUnitary) {n v : ℕ} {hn : 0 < n} {hv : 0 < v} {x y s : ℝ}
    (h : (tadicCenteredSegment τ v hv x).twist s = tadicCenteredSegment ρ n hn y) :
    τ = ρ ∧ v = n ∧ s + x = y := by
  have hl := congrArg Segment.length h
  simp only [Segment.twist_length, tadicCenteredSegment_length] at hl
  subst hl
  have hb := congrArg Segment.base h
  simp only [tadicCenteredSegment, Segment.twist, CuspidalDatum.twist_twist] at hb
  obtain ⟨rfl, he⟩ := cuspidalDatum_eq_of_twist_eq_of_isUnitary hρ hτ hb
  exact ⟨rfl, rfl, by linarith⟩

theorem tadicCenteredSegment_injective (ρ : T.CuspidalDatum.{uV, uF}) {n : ℕ} (hn : 0 < n)
    {x y : ℝ} (h : tadicCenteredSegment ρ n hn x = tadicCenteredSegment ρ n hn y) : x = y := by
  have hb := congrArg Segment.base h
  simp only [tadicCenteredSegment] at hb
  have := cuspidalDatum_twist_injective ρ hb
  linarith

open Classical in
/-- The number of segments centered at `0` or at `1/2`. -/
def tadicCentralCount (ρ : T.CuspidalDatum.{uV, uF}) (n : ℕ) (hn : 0 < n)
    (a : T.Multisegment.{uV, uF}) : ℕ :=
  Multiset.countP (fun Δ => Δ = tadicCenteredSegment ρ n hn 0 ∨
    Δ = tadicCenteredSegment ρ n hn (1 / 2)) a

open Classical in
theorem tadicCentralCount_add (ρ : T.CuspidalDatum.{uV, uF}) (n : ℕ) (hn : 0 < n)
    (a b : T.Multisegment.{uV, uF}) :
    tadicCentralCount ρ n hn (a + b) = tadicCentralCount ρ n hn a + tadicCentralCount ρ n hn b :=
  Multiset.countP_add _ _ _

open Classical in
theorem tadicCentralCount_sum (ρ : T.CuspidalDatum.{uV, uF}) (n : ℕ) (hn : 0 < n) {k : ℕ}
    (c : Fin k → T.Multisegment.{uV, uF}) :
    tadicCentralCount ρ n hn (∑ i, c i) = ∑ i, tadicCentralCount ρ n hn (c i) := by
  unfold tadicCentralCount
  exact map_sum (Multiset.countPAddMonoidHom _) c Finset.univ

/-- `a(u,n)^ρ` has exactly one segment centered at `0` or `1/2`. -/
theorem tadicCentralCount_tadicMultisegment (ρ : T.CuspidalDatum.{uV, uF}) {u n : ℕ}
    (hu : 0 < u) (hn : 0 < n) : tadicCentralCount ρ n hn (tadicMultisegment ρ u n hn) = 1 := by
  classical
  unfold tadicCentralCount tadicMultisegment
  rw [Multiset.countP_map]
  have hq : ∀ j ∈ Multiset.range u,
      (tadicCenteredSegment ρ n hn ((j : ℝ) - ((u : ℝ) - 1) / 2) =
          tadicCenteredSegment ρ n hn 0 ∨
        tadicCenteredSegment ρ n hn ((j : ℝ) - ((u : ℝ) - 1) / 2) =
          tadicCenteredSegment ρ n hn (1 / 2)) ↔ (2 * j + 1 = u ∨ 2 * j = u) := by
    intro j _
    constructor
    · rintro (h | h)
      · have h' := tadicCenteredSegment_injective ρ hn h
        left
        have : ((2 * j + 1 : ℕ) : ℝ) = u := by push_cast; linarith
        exact_mod_cast this
      · have h' := tadicCenteredSegment_injective ρ hn h
        right
        have : ((2 * j : ℕ) : ℝ) = u := by push_cast; linarith
        exact_mod_cast this
    · rintro (h | h)
      · left
        have : ((2 * j + 1 : ℕ) : ℝ) = u := by exact_mod_cast h
        push_cast at this
        congr 1
        linarith
      · right
        have : ((2 * j : ℕ) : ℝ) = u := by exact_mod_cast h
        push_cast at this
        congr 1
        linarith
  rw [Multiset.filter_congr hq]
  have hf : Multiset.filter (fun j => 2 * j + 1 = u ∨ 2 * j = u) (Multiset.range u) =
      {u / 2} := by
    refine ((Multiset.nodup_range u).filter _).ext (Multiset.nodup_singleton _) |>.mpr ?_
    intro j
    simp only [Multiset.mem_filter, Multiset.mem_range, Multiset.mem_singleton]
    omega
  rw [hf, Multiset.card_singleton]

/-- Tadić's combinatorial step in A.10: for unitary `ρ`, `a(d,n)^ρ` is not a sum of
Tadić head pieces of degree at most `m < deg a(d,n)^ρ`. -/
theorem not_sum_tadicHeadPieces {ρ : T.CuspidalDatum.{uV, uF}} (hρ : ρ.IsUnitary) {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) {m : ℕ} (hm : m < (tadicMultisegment ρ d n hn).degree) {k : ℕ}
    (c : Fin k → T.Multisegment.{uV, uF}) (hc : ∀ i, IsTadicHeadPiece m (c i))
    (hsum : ∑ i, c i = tadicMultisegment ρ d n hn) : False := by
  classical
  have hle : ∀ i, c i ≤ tadicMultisegment ρ d n hn := fun i =>
    hsum ▸ Finset.single_le_sum (f := c) (fun j _ => zero_le) (Finset.mem_univ i)
  have hpiece : ∀ i, ∃ u, 0 < u ∧ c i = tadicMultisegment ρ u n hn ∧ (c i).degree ≤ m := by
    intro i
    obtain ⟨τ, u, v, hv, hu, hτ, ⟨hci, hdeg⟩ | ⟨s, hs0, hs1, hci⟩⟩ := hc i
    · have hmem : tadicCenteredSegment τ v hv (((0 : ℕ) : ℝ) - ((u : ℝ) - 1) / 2) ∈ c i := by
        rw [hci]
        exact mem_tadicMultisegment.mpr ⟨0, hu, rfl⟩
      obtain ⟨j, -, hjeq⟩ := mem_tadicMultisegment.mp (Multiset.mem_of_le (hle i) hmem)
      obtain ⟨rfl, rfl, -⟩ := tadicCenteredSegment_twist_eq hρ hτ (s := 0)
        (by rw [Segment.twist_zero]; exact hjeq.symm)
      exact ⟨u, hu, hci, hdeg⟩
    · exfalso
      have hmem : (tadicCenteredSegment τ v hv (((0 : ℕ) : ℝ) - ((u : ℝ) - 1) / 2)).twist s ∈
          c i := by
        rw [hci]
        exact Multiset.mem_map_of_mem (Segment.twist s) (mem_tadicMultisegment.mpr ⟨0, hu, rfl⟩)
      obtain ⟨j, -, hjeq⟩ := mem_tadicMultisegment.mp (Multiset.mem_of_le (hle i) hmem)
      obtain ⟨rfl, rfl, hx⟩ := tadicCenteredSegment_twist_eq hρ hτ hjeq.symm
      have hz : ((((2 * j + u : ℕ) : ℤ) - (d : ℤ) : ℤ) : ℝ) = 2 * s := by
        push_cast at hx ⊢
        linarith
      have hzabs : |((((2 * j + u : ℕ) : ℤ) - (d : ℤ) : ℤ) : ℝ)| < 1 := by
        rw [hz, abs_mul, abs_two]
        linarith
      have hz0 : (((2 * j + u : ℕ) : ℤ) - (d : ℤ) : ℤ) = 0 :=
        Int.abs_lt_one_iff.mp (by exact_mod_cast hzabs)
      have hs : s = 0 := by
        have : ((((2 * j + u : ℕ) : ℤ) - (d : ℤ) : ℤ) : ℝ) = 0 := by exact_mod_cast hz0
        linarith
      rw [hs, abs_zero] at hs0
      exact lt_irrefl _ hs0
  choose u hu hcu hdeg using hpiece
  have hone : ∀ i, tadicCentralCount ρ n hn (c i) = 1 := fun i => by
    rw [hcu i]
    exact tadicCentralCount_tadicMultisegment ρ (hu i) hn
  have hcount := congrArg (tadicCentralCount ρ n hn) hsum
  rw [tadicCentralCount_sum, tadicCentralCount_tadicMultisegment ρ hd hn,
    Finset.sum_congr rfl (fun i _ => hone i)] at hcount
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at hcount
  subst hcount
  have h0 : c 0 = tadicMultisegment ρ d n hn := by simpa using hsum
  have := hdeg 0
  rw [h0] at this
  omega

end Langlands.Classification
