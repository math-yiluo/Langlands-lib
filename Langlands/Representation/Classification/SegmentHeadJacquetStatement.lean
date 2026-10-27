import Langlands.Representation.Classification.Segments
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Tensor.Finite

/-!
# Two-block Jacquet modules of special segment heads

Zelevinsky 1980, Proposition 9.5, for the strong head of the increasing segment
induction: the normalized Jacquet module along an ordered two-block split
`(n - l, l)` vanishes unless the cuspidal rank divides `l`, and for `l = q r` it is
the external tensor product of the heads of the terminal and initial subsegments,
in that order. This file states the formula as a proposition; it proves nothing
about it.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV

namespace GeneralLinear.BlockShape

/-- The ordered two-block shape `(a, b)` of `GL_n`, for positive `a, b` with
`a + b = n`; its standard parabolic is the upper block-triangular one. -/
def ofPair {n : ℕ} (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a + b = n) : BlockShape n where
  length := 2
  size := ![a, b]
  positive := by
    intro i
    fin_cases i <;> assumption
  sum_eq := by simpa [Fin.sum_univ_two] using h

@[simp]
theorem ofPair_length {n : ℕ} (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a + b = n) :
    (ofPair a b ha hb h).length = 2 := rfl

@[simp]
theorem ofPair_size_zero {n : ℕ} (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a + b = n) :
    (ofPair a b ha hb h).size (0 : Fin 2) = a := rfl

@[simp]
theorem ofPair_size_one {n : ℕ} (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a + b = n) :
    (ofPair a b ha hb h).size (1 : Fin 2) = b := rfl

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData.Segment

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The initial subsegment `[ρ, ν^(q-1) ρ]` of `Δ = [ρ, ν^(m-1) ρ]`, for `0 < q`. -/
def initial (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) : Segment.{uV, uF} T where
  base := Δ.base
  length := q
  length_pos := hq

/-- The terminal subsegment `[ν^q ρ, ν^(m-1) ρ]` of `Δ = [ρ, ν^(m-1) ρ]`, for `q < m`. -/
def terminal (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : q < Δ.length) : Segment.{uV, uF} T where
  base := Δ.member q
  length := Δ.length - q
  length_pos := Nat.sub_pos_of_lt hq

@[simp]
theorem initial_base (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) :
    (Δ.initial q hq).base = Δ.base := rfl

@[simp]
theorem initial_length (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) :
    (Δ.initial q hq).length = q := rfl

@[simp]
theorem initial_rank (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) :
    (Δ.initial q hq).rank = Δ.rank := rfl

theorem initial_degree (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) :
    (Δ.initial q hq).degree = q * Δ.rank := rfl

/-- The `i`-th element of the initial subsegment is `ν^i ρ`. -/
theorem initial_member (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) (i : ℕ) :
    (Δ.initial q hq).member i = Δ.member i := rfl

@[simp]
theorem terminal_base (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : q < Δ.length) :
    (Δ.terminal q hq).base = Δ.base.twist (q : ℝ) := rfl

@[simp]
theorem terminal_length (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : q < Δ.length) :
    (Δ.terminal q hq).length = Δ.length - q := rfl

@[simp]
theorem terminal_rank (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : q < Δ.length) :
    (Δ.terminal q hq).rank = Δ.rank := rfl

theorem terminal_degree (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : q < Δ.length) :
    (Δ.terminal q hq).degree = (Δ.length - q) * Δ.rank := rfl

/-- The `i`-th element of the terminal subsegment is `ν^(q+i) ρ`. -/
theorem terminal_member (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : q < Δ.length) (i : ℕ) :
    (Δ.terminal q hq).member i = Δ.member (q + i) := by
  simp only [member, terminal, CuspidalDatum.twist_twist, Nat.cast_add, add_comm]

/-- The terminal subsegment ends where `Δ` ends, at `ν^(m-1) ρ`. -/
theorem terminal_last (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : q < Δ.length) :
    (Δ.terminal q hq).last = Δ.last := by
  rw [last, terminal_member, last, terminal_length]
  congr 1
  omega

/-- The two subsegments fill the degree of `Δ`: `(m - q) r + q r = m r`. -/
theorem terminal_degree_add_initial_degree (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length) :
    (Δ.terminal q hqm).degree + (Δ.initial q hq).degree = Δ.degree := by
  rw [terminal_degree, initial_degree, ← Nat.add_mul, Nat.sub_add_cancel hqm.le]

/-- The ordered two-block shape `((m - q) r, q r)` of `GL_{mr}`, for `0 < q < m`. -/
def splitShape (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length) :
    GeneralLinear.BlockShape Δ.degree :=
  GeneralLinear.BlockShape.ofPair (Δ.terminal q hqm).degree (Δ.initial q hq).degree
    (Δ.terminal q hqm).degree_pos (Δ.initial q hq).degree_pos
    (Δ.terminal_degree_add_initial_degree q hq hqm)

/-- `splitShape` is the split `(n - l, l)` of `n = m r` at `l = q r`. -/
theorem splitShape_eq_ofPair (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length) (hl : 0 < Δ.degree - q * Δ.rank) :
    Δ.splitShape q hq hqm =
      GeneralLinear.BlockShape.ofPair (Δ.degree - q * Δ.rank) (q * Δ.rank) hl
        (Nat.mul_pos hq Δ.rank_pos)
        (Nat.sub_add_cancel (Nat.mul_le_mul_right _ hqm.le)) := by
  unfold splitShape
  congr 1
  rw [terminal_degree, Nat.sub_mul]

section Factors

variable (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length)

/-- The ordered pair of block factors `(π₁, π₂)` of `splitShape`: `π₁` on the first
block `GL_{(m-q) r}` and `π₂` on the second block `GL_{q r}`. -/
def splitFactors
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.terminal q hqm).degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.initial q hq).degree F.Carrier)) :
    letI := T.topology
    ∀ i : Fin (Δ.splitShape q hq hqm).length,
      SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear ((Δ.splitShape q hq hqm).size i) F.Carrier) :=
  Fin.cons π₁ (Fin.cons π₂ finZeroElim)

end Factors

end PadicField.TopologicalData.Segment

namespace Classification

open GeneralLinear PadicField.TopologicalData

/-- Zelevinsky 1980, Proposition 9.5, for the strong head `π` of the increasing
segment induction `i(ρ, νρ, …, ν^(m-1) ρ)` on `GL_n`, `n = m r`, `r` the cuspidal
rank. For every ordered proper split `(n - l, l)`, `0 < l < n`, the actual normalized
Jacquet module is zero when `r ∤ l`; for `0 < q < m` the normalized Jacquet module
along `((m - q) r, q r)` is isomorphic to the external tensor product of a head of
the terminal segment `[ν^q ρ, ν^(m-1) ρ]` (first block) and a head of the initial
segment `[ρ, ν^(q-1) ρ]` (second block). -/
def SegmentHeadJacquetFormula {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV, uF} T)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentHead Δ π →
      (∀ (l : ℕ) (hl : 0 < l) (hln : l < Δ.degree), ¬ Δ.rank ∣ l →
        Subsingleton ((T.normalizedJacquetFunctor
          (BlockShape.ofPair (Δ.degree - l) l (Nat.sub_pos_of_lt hln) hl
            (Nat.sub_add_cancel hln.le))).obj π)) ∧
      (∀ (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length),
        ∃ (π₁ : SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear (Δ.terminal q hqm).degree F.Carrier))
          (π₂ : SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear (Δ.initial q hq).degree F.Carrier)),
          T.IsSegmentHead (Δ.terminal q hqm) π₁ ∧ T.IsSegmentHead (Δ.initial q hq) π₂ ∧
            Nonempty ((T.normalizedJacquetFunctor (Δ.splitShape q hq hqm)).obj π ≅
              FiniteTensor.externalFunctor.obj (Δ.splitFactors q hq hqm π₁ π₂)))

end Classification

end Langlands
