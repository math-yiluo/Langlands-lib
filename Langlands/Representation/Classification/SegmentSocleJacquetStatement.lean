import Langlands.Representation.Classification.SegmentHeadJacquetStatement

/-!
# Two-block Jacquet modules of segment socles

Zelevinsky 1980, Proposition 3.4, for the unique irreducible subrepresentation of the
increasing segment induction: the normalized Jacquet module along an ordered
two-block split `(l, n - l)` vanishes unless the cuspidal rank divides `l`, and for
`l = q r` it is the external tensor product of the socles of the initial and
terminal subsegments, in that order. This file states the formula as a proposition;
it proves nothing about it.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV

namespace PadicField.TopologicalData.Segment

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The two subsegments fill the degree of `Δ`: `q r + (m - q) r = m r`. -/
theorem initial_degree_add_terminal_degree (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length) :
    (Δ.initial q hq).degree + (Δ.terminal q hqm).degree = Δ.degree := by
  rw [Nat.add_comm]
  exact Δ.terminal_degree_add_initial_degree q hq hqm

/-- The ordered two-block shape `(q r, (m - q) r)` of `GL_{mr}`, for `0 < q < m`. -/
def socleSplitShape (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length) :
    GeneralLinear.BlockShape Δ.degree :=
  GeneralLinear.BlockShape.ofPair (Δ.initial q hq).degree (Δ.terminal q hqm).degree
    (Δ.initial q hq).degree_pos (Δ.terminal q hqm).degree_pos
    (Δ.initial_degree_add_terminal_degree q hq hqm)

/-- `socleSplitShape` is the split `(l, n - l)` of `n = m r` at `l = q r`. -/
theorem socleSplitShape_eq_ofPair (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length) (hl : 0 < Δ.degree - q * Δ.rank) :
    Δ.socleSplitShape q hq hqm =
      GeneralLinear.BlockShape.ofPair (q * Δ.rank) (Δ.degree - q * Δ.rank)
        (Nat.mul_pos hq Δ.rank_pos) hl
        (Nat.add_sub_of_le (Nat.mul_le_mul_right _ hqm.le)) := by
  unfold socleSplitShape
  congr 1
  rw [terminal_degree, Nat.sub_mul]

section Factors

variable (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length)

/-- The ordered pair of block factors `(π₁, π₂)` of `socleSplitShape`: `π₁` on the
first block `GL_{q r}` and `π₂` on the second block `GL_{(m-q) r}`. -/
def socleSplitFactors
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.initial q hq).degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.terminal q hqm).degree F.Carrier)) :
    letI := T.topology
    ∀ i : Fin (Δ.socleSplitShape q hq hqm).length,
      SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear ((Δ.socleSplitShape q hq hqm).size i) F.Carrier) :=
  Fin.cons π₁ (Fin.cons π₂ finZeroElim)

end Factors

end PadicField.TopologicalData.Segment

namespace Classification

open GeneralLinear PadicField.TopologicalData

/-- Zelevinsky 1980, Proposition 3.4, for the unique irreducible subrepresentation `π`
of the increasing segment induction `i(ρ, νρ, …, ν^(m-1) ρ)` on `GL_n`, `n = m r`,
`r` the cuspidal rank. For every ordered proper split `(l, n - l)`, `0 < l < n`, the
actual normalized Jacquet module is zero when `r ∤ l`; for `0 < q < m` the normalized
Jacquet module along `(q r, (m - q) r)` is isomorphic to the external tensor product
of a socle of the initial segment `[ρ, ν^(q-1) ρ]` (first block) and a socle of the
terminal segment `[ν^q ρ, ν^(m-1) ρ]` (second block). -/
def SegmentSocleJacquetFormula {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV, uF} T)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentSocle Δ π →
      (∀ (l : ℕ) (hl : 0 < l) (hln : l < Δ.degree), ¬ Δ.rank ∣ l →
        Subsingleton ((T.normalizedJacquetFunctor
          (BlockShape.ofPair l (Δ.degree - l) hl (Nat.sub_pos_of_lt hln)
            (Nat.add_sub_of_le hln.le))).obj π)) ∧
      (∀ (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length),
        ∃ (π₁ : SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear (Δ.initial q hq).degree F.Carrier))
          (π₂ : SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear (Δ.terminal q hqm).degree F.Carrier)),
          T.IsSegmentSocle (Δ.initial q hq) π₁ ∧ T.IsSegmentSocle (Δ.terminal q hqm) π₂ ∧
            Nonempty ((T.normalizedJacquetFunctor (Δ.socleSplitShape q hq hqm)).obj π ≅
              FiniteTensor.externalFunctor.obj (Δ.socleSplitFactors q hq hqm π₁ π₂)))

end Classification

end Langlands
