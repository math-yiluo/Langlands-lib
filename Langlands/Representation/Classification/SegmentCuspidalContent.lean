import Langlands.Representation.Classification.Segments

/-!
# Cuspidal content of segments and multisegments

Record every indexed member of a segment and sum these multisets over a
multisegment. All occurrences are retained, without a distinctness assumption.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uV uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- The cuspidal members of a segment, with one occurrence for each index. -/
def cuspidalContent (Δ : Segment.{uV, uF} T) : Multiset (CuspidalDatum.{uV, uF} T) :=
  (List.ofFn (fun i : Fin Δ.length => Δ.member (i : ℕ)) : Multiset _)

@[simp]
theorem mem_cuspidalContent (Δ : Segment.{uV, uF} T) (ρ : CuspidalDatum.{uV, uF} T) :
    ρ ∈ Δ.cuspidalContent ↔ ρ ∈ Δ.support := by
  simp only [cuspidalContent, Multiset.mem_coe, List.mem_ofFn, support, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hi, hρ⟩
    exact ⟨⟨i, hi⟩, hρ⟩

@[simp]
theorem card_cuspidalContent (Δ : Segment.{uV, uF} T) :
    Δ.cuspidalContent.card = Δ.length := by
  simp [cuspidalContent]

@[simp]
theorem sum_rank_cuspidalContent (Δ : Segment.{uV, uF} T) :
    (Δ.cuspidalContent.map CuspidalDatum.rank).sum = Δ.degree := by
  simp [cuspidalContent, List.map_ofFn, Function.comp_def, member, CuspidalDatum.twist, degree, rank]

/-- A segment of length one contributes its base exactly once. -/
theorem cuspidalContent_of_length_one (Δ : Segment.{uV, uF} T) (h : Δ.length = 1) :
    Δ.cuspidalContent = {Δ.base} := by
  simp [cuspidalContent, h]

@[simp]
theorem cuspidalContent_singleton (ρ : CuspidalDatum.{uV, uF} T) :
    (Segment.mk ρ 1 Nat.one_pos).cuspidalContent = {ρ} :=
  cuspidalContent_of_length_one _ rfl

end Segment

namespace Multisegment

/-- The sum of the cuspidal contents of all segment occurrences. -/
def cuspidalContent (a : Multisegment.{uV, uF} T) : Multiset (CuspidalDatum.{uV, uF} T) :=
  (a.map Segment.cuspidalContent).sum

@[simp]
theorem cuspidalContent_zero :
    (0 : Multisegment.{uV, uF} T).cuspidalContent = 0 := by
  simp [cuspidalContent]

@[simp]
theorem cuspidalContent_singleton (Δ : Segment.{uV, uF} T) :
    ({Δ} : Multisegment.{uV, uF} T).cuspidalContent = Δ.cuspidalContent := by
  simp [cuspidalContent]

@[simp]
theorem cuspidalContent_cons (Δ : Segment.{uV, uF} T) (a : Multisegment.{uV, uF} T) :
    cuspidalContent (Δ ::ₘ a) = Δ.cuspidalContent + a.cuspidalContent := by
  simp [cuspidalContent]

@[simp]
theorem cuspidalContent_add (a b : Multisegment.{uV, uF} T) :
    (a + b).cuspidalContent = a.cuspidalContent + b.cuspidalContent := by
  simp [cuspidalContent, Multiset.map_add, Multiset.sum_add]

@[simp]
theorem sum_rank_cuspidalContent (a : Multisegment.{uV, uF} T) :
    (a.cuspidalContent.map CuspidalDatum.rank).sum = a.degree := by
  induction a using Multiset.induction_on with
  | empty => simp [degree]
  | cons Δ a ih =>
    simp [cuspidalContent_cons, Multiset.map_add, Multiset.sum_add, ih, degree]

end Multisegment

end Langlands.PadicField.TopologicalData
