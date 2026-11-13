import Langlands.Representation.Classification.SpehNeighborMWBound

/-! # Integer models for actual rank-lower neighboring rectangles -/

noncomputable section

namespace Langlands.MoeglinWaldspurger

open PadicField.TopologicalData
open scoped Classical

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A segment with an integral beginning on a fixed line is an interval realization. -/
theorem exists_interval_of_integer_beginning
    (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (Δ : T.Segment.{uV, uF})
    (h : ∃ b : ℤ, Δ.base = ρ.twist (x + (b : ℝ))) :
    ∃ I : Interval, I.realize ρ x = Δ := by
  obtain ⟨b, hb⟩ := h
  let I : Interval := ⟨b, b + (Δ.length : ℤ) - 1, by
    have := Δ.length_pos
    omega⟩
  refine ⟨I, Segment.ext_base_length ?_ ?_⟩
  · exact hb.symm
  · change (b + (Δ.length : ℤ) - 1 - b).toNat + 1 = Δ.length
    have := Δ.length_pos
    omega

/-- Recover an integer multisegment occurrence by occurrence, retaining multiplicity. -/
theorem exists_integer_model
    (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ)
    (b : T.Multisegment.{uV, uF})
    (h : ∀ Δ ∈ b, ∃ z : ℤ, Δ.base = ρ.twist (x + (z : ℝ))) :
    ∃ a : Multisegment, realize ρ x a = b := by
  revert h
  induction b using Multiset.induction_on with
  | empty =>
    intro _
    exact ⟨0, rfl⟩
  | cons Δ b ih =>
    intro h
    obtain ⟨I, hI⟩ := exists_interval_of_integer_beginning ρ x Δ
      (h Δ (Multiset.mem_cons_self Δ b))
    obtain ⟨a, ha⟩ := ih (fun Γ hΓ =>
      h Γ (Multiset.mem_cons_of_mem hΓ))
    refine ⟨I ::ₘ a, ?_⟩
    simp only [realize, Multiset.map_cons]
    change I.realize ρ x ::ₘ realize ρ x a = Δ ::ₘ b
    rw [hI, ha]

/-- An occurrence-preserving integer model of actual segments on one integral line. -/
def integerModel
    (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ)
    (b : T.Multisegment.{uV, uF})
    (h : ∀ Δ ∈ b, ∃ z : ℤ, Δ.base = ρ.twist (x + (z : ℝ))) : Multisegment :=
  (exists_integer_model ρ x b h).choose

@[simp] theorem realize_integerModel
    (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ)
    (b : T.Multisegment.{uV, uF})
    (h : ∀ Δ ∈ b, ∃ z : ℤ, Δ.base = ρ.twist (x + (z : ℝ))) :
    realize ρ x (integerModel ρ x b h) = b :=
  (exists_integer_model ρ x b h).choose_spec

/-- The inherited beginnings of every rank-lower neighbor label are integral
at the ending offset used in the MW bound. -/
theorem integer_beginnings_of_rankLE_neighbor_rectangles
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hk : 2 ≤ k)
    {b : T.Multisegment.{uV, uF}}
    (h : PadicField.TopologicalData.Multisegment.RankLE b
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega))) :
    ∀ Δ ∈ b, ∃ z : ℤ,
      Δ.base = ρ.twist ((((k : ℝ) - l - 1) / 2) + (z : ℝ)) := by
  intro Δ hΔ
  have hm := Multiset.mem_of_le h.beginnings_le
    (Multiset.mem_map.mpr ⟨Δ, hΔ, rfl⟩)
  obtain ⟨Γ, hΓ, heΓ⟩ := Multiset.mem_map.mp hm
  obtain ⟨j, -, hej⟩ :=
    Classification.beginning_index_neighbor_rectangles ρ l k hk Γ hΓ
  refine ⟨(j : ℤ) + 1 - (k : ℤ), (heΓ.symm.trans hej).trans ?_⟩
  congr 1
  push_cast
  ring

/-- The integer MW input corresponding to an actual rank-lower neighbor label. -/
def neighborIntegerModel
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hk : 2 ≤ k)
    {b : T.Multisegment.{uV, uF}}
    (h : PadicField.TopologicalData.Multisegment.RankLE b
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega))) : Multisegment :=
  integerModel ρ (((k : ℝ) - l - 1) / 2) b
    (integer_beginnings_of_rankLE_neighbor_rectangles ρ l k hk h)

@[simp] theorem realize_neighborIntegerModel
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hk : 2 ≤ k)
    {b : T.Multisegment.{uV, uF}}
    (h : PadicField.TopologicalData.Multisegment.RankLE b
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega))) :
    realize ρ (((k : ℝ) - l - 1) / 2) (neighborIntegerModel ρ l k hk h) = b :=
  realize_integerModel _ _ _ _

/-- The integer dual of an actual rank-lower neighbor label has the required
length bound, conditional only on the explicit ending-bound proposition. -/
theorem dual_lengths_le_neighborIntegerModel (hP : EndingBound)
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {b : T.Multisegment.{uV, uF}}
    (h : PadicField.TopologicalData.Multisegment.RankLE b
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega))) :
    ∀ I ∈ dual (neighborIntegerModel ρ l k hk h), I.length ≤ l := by
  apply dual_lengths_le_neighbor_rectangles hP ρ l k hl hk
  simpa only [realize_neighborIntegerModel] using h

/-- Realization preserves the conditional dual-length bound on actual segments. -/
theorem realized_dual_lengths_le_neighborIntegerModel (hP : EndingBound)
    (ρ : T.CuspidalDatum.{uV, uF}) (l k : ℕ) (hl : 0 < l) (hk : 2 ≤ k)
    {b : T.Multisegment.{uV, uF}}
    (h : PadicField.TopologicalData.Multisegment.RankLE b
      (Classification.tadicMultisegment ρ l (k + 1) (by omega) +
        Classification.tadicMultisegment ρ l (k - 1) (by omega))) :
    ∀ Δ ∈ realize ρ (((k : ℝ) - l - 1) / 2)
        (dual (neighborIntegerModel ρ l k hk h)), Δ.length ≤ l := by
  intro Δ hΔ
  obtain ⟨I, hI, rfl⟩ := Multiset.mem_map.mp hΔ
  exact dual_lengths_le_neighborIntegerModel hP ρ l k hl hk h I hI

end Langlands.MoeglinWaldspurger
