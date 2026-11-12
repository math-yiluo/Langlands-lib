import Langlands.Representation.Classification.MoeglinWaldspurger
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.SegmentSocleInversionReduction
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # Realizing integer-line MW multisegments as actual cuspidal segments -/

noncomputable section

namespace Langlands.MoeglinWaldspurger

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Interval

/-- Realize `[b,e]` as `[ν^(x+b)ρ,...,ν^(x+e)ρ]`, using the actual segment twist. -/
def realize (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) :
    T.Segment.{uV, uF} :=
  (⟨ρ, I.length, I.length_pos⟩ : T.Segment).twist (x + (I.beginning : ℝ))

@[simp] theorem realize_base (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) :
    (I.realize ρ x).base = ρ.twist (x + (I.beginning : ℝ)) := rfl

@[simp] theorem realize_length (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) :
    (I.realize ρ x).length = I.length := rfl

@[simp] theorem realize_rank (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) :
    (I.realize ρ x).rank = ρ.rank := rfl

theorem realize_member (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) (i : ℕ) :
    (I.realize ρ x).member i = ρ.twist (x + ((I.beginning : ℝ) + (i : ℝ))) := by
  simp only [Segment.member, realize_base, CuspidalDatum.twist_twist]
  congr 1
  ring

@[simp] theorem realize_last (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) :
    (I.realize ρ x).last = ρ.twist (x + (I.ending : ℝ)) := by
  rw [Segment.last, realize_length, realize_member]
  have hn : (I.length - 1 : ℕ) = (I.ending - I.beginning).toNat := by
    simp [length]
  have hz : ((I.ending - I.beginning).toNat : ℤ) = I.ending - I.beginning :=
    Int.toNat_of_nonneg (sub_nonneg.mpr I.nonempty)
  have hr : ((I.ending - I.beginning).toNat : ℝ) =
      (I.ending : ℝ) - (I.beginning : ℝ) := by exact_mod_cast hz
  rw [hn, hr]
  congr 1
  ring

theorem realize_cuspidalContent (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) :
    (I.realize ρ x).cuspidalContent =
      I.support.map (fun (z : ℤ) => ρ.twist (x + (z : ℝ))) := by
  unfold Segment.cuspidalContent support
  rw [Multiset.map_map, ← Multiset.coe_range, Multiset.map_coe]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range,
      Function.comp_apply, realize_member]
    congr 1
    push_cast
    rfl

end Interval

/-- Realize each occurrence on the same actual cuspidal line with real offset `x`. -/
def realize (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a : Multisegment) :
    T.Multisegment.{uV, uF} := a.map (Interval.realize ρ x)

@[simp] theorem realize_zero (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) :
    realize ρ x 0 = 0 := rfl

@[simp] theorem realize_add (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a b : Multisegment) :
    realize ρ x (a + b) = realize ρ x a + realize ρ x b := by simp [realize]

@[simp] theorem realize_card (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a : Multisegment) :
    (realize ρ x a).card = a.card := by simp [realize]

theorem realize_degree (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a : Multisegment) :
    (realize ρ x a).degree = weight a * ρ.rank := by
  induction a using Multiset.induction_on with
  | empty => simp [realize, Multisegment.degree]
  | cons I a ih =>
    simpa [realize, Multisegment.degree, weight, Segment.degree, Nat.add_mul] using
      congrArg (fun n => I.length * ρ.rank + n) ih

theorem support_card (a : Multisegment) : (support a).card = weight a := by
  induction a using Multiset.induction_on with
  | empty => rfl
  | cons I a ih =>
    simp only [support, Multiset.cons_bind, Multiset.card_add] at *
    rw [ih, weight_cons]
    simp [Interval.support]

theorem realize_cuspidalContent (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a : Multisegment) :
    (realize ρ x a).cuspidalContent =
      (support a).map (fun (z : ℤ) => ρ.twist (x + (z : ℝ))) := by
  induction a using Multiset.induction_on with
  | empty => simp [realize, support]
  | cons I a ih =>
    simpa only [realize, Multiset.map_cons, Multisegment.cuspidalContent_cons,
      support, Multiset.cons_bind, Multiset.map_add, Interval.realize_cuspidalContent] using
      congrArg (fun m => I.support.map (fun (z : ℤ) => ρ.twist (x + (z : ℝ))) + m) ih

/-- Equality of combinatorial supports supplies the actual same-rank transport. -/
theorem realize_degree_eq_of_support_eq (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ)
    {a b : Multisegment} (h : support a = support b) :
    (realize ρ x a).degree = (realize ρ x b).degree := by
  have hw : weight a = weight b := by simpa [support_card] using congrArg Multiset.card h
  simp only [realize_degree, hw]

/-- Actual Langlands-head data determine the rank of the represented GL group. -/
theorem langlandsHead_degree {a : T.Multisegment.{uV, uF}} {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : a.IsLanglandsHead π) : a.degree = n := by
  obtain ⟨d, rfl, _⟩ := h
  exact d.multisegment_degree

/-- The actual head relation supplies irreducibility, hence finite length. -/
theorem langlandsHead_isIrreducible {a : T.Multisegment.{uV, uF}} {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : a.IsLanglandsHead π) : letI := T.topology
      π.IsIrreducible := by
  obtain ⟨d, _, _, _, hπ⟩ := h
  exact hπ.1

end Langlands.MoeglinWaldspurger
