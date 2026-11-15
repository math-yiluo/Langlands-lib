import Langlands.Representation.Classification.SpehNeighborRectangleReduction
import Langlands.Representation.Classification.MoeglinWaldspurgerRectangleDual
import Langlands.Representation.Classification.MoeglinWaldspurgerAubertStatement
import Langlands.Representation.Classification.SpehNeighborIntegerModel
import Langlands.Representation.Classification.MoeglinWaldspurgerEndingBoundProof
import Langlands.Representation.Classification.MoeglinWaldspurgerSupportProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadExistenceProof
import Langlands.Representation.Classification.TadicSocleIndependence
import Langlands.Representation.Aubert.AdjustedInvolutivityProof
import Langlands.Representation.Aubert.AdjustedProductConstituents

/-! # The neighboring-rectangle constituent length bound from MW correctness -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Classification.SpehNeighborProduct

open PadicField.TopologicalData SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A rectangle with `r` rows of `d` points, realized at the centering offset,
is Tadić's `a(r,d)^ρ`. -/
theorem realize_rectangle_tadic (ρ : T.CuspidalDatum.{max uF uV, uF}) (b : ℤ) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (x : ℝ) (hx : x + (b : ℝ) = -((r : ℝ) + d - 2) / 2) :
    MoeglinWaldspurger.realize ρ x (MoeglinWaldspurger.rectangle b (r - 1) (d - 1)) =
      tadicMultisegment ρ r d hd := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  apply MoeglinWaldspurger.realize_rectangle
  rw [hx]
  push_cast
  ring

/-- The MW dual of the same rectangle realizes Tadić's transposed `a(d,r)^ρ`. -/
theorem realize_dual_rectangle_tadic (ρ : T.CuspidalDatum.{max uF uV, uF}) (b : ℤ) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (x : ℝ) (hx : x + (b : ℝ) = -((r : ℝ) + d - 2) / 2) :
    MoeglinWaldspurger.realize ρ x
        (MoeglinWaldspurger.dual (MoeglinWaldspurger.rectangle b (r - 1) (d - 1))) =
      tadicMultisegment ρ d r hr := by
  rw [MoeglinWaldspurger.dual_rectangle]
  exact realize_rectangle_tadic F T ρ b d r hd hr x (by rw [hx]; ring)

/-- A weak Langlands quotient of a segment datum is an actual Langlands head of
its multisegment. -/
theorem isLanglandsHead_of_isLanglandsQuotient {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (h : d.IsLanglandsQuotient π) : d.multisegment.IsLanglandsHead π := by
  let := T.topology
  obtain ⟨E, hE⟩ := orderedMultisegmentHeadExistence.{uF, uV} F T n d h.1 h.2.1
  obtain ⟨e⟩ := (orderedMultisegmentHeadClassification.{uF, uV} F T n d d E π
    hE.isLanglandsQuotient h).mp rfl
  exact Multisegment.IsLanglandsHead.of_iso ⟨d, rfl, hE⟩ e

/-- Every multisegment of the prescribed degree has an actual Langlands head. -/
theorem exists_isLanglandsHead (a : T.Multisegment.{max uF uV, uF}) {n : ℕ}
    (hn : a.degree = n) :
    letI := T.topology
    ∃ (d : T.SegmentProductDatum.{max uF uV, uF} n)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      d.multisegment = a ∧ d.IsLanglandsHead π := by
  let := T.topology
  subst n
  obtain ⟨π, d, hd, hπ⟩ := multisegmentHeadExistence.{uF, uV} F T a
  exact ⟨d, π, hd, hπ⟩

/-- Under MW correctness, the Langlands quotient of a realized integer
multisegment has, as adjusted Aubert dual, a Langlands quotient of the
realized MW dual. -/
theorem exists_adjusted_realize_dual
    (hMW : MoeglinWaldspurger.AubertCorrectness.{uF, max uF uV} F T)
    (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ) (a : MoeglinWaldspurger.Multisegment)
    {n : ℕ} (dA : T.SegmentProductDatum.{max uF uV, uF} n)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hdA : dA.multisegment = MoeglinWaldspurger.realize ρ x a)
    (hA : dA.IsLanglandsQuotient A) :
    letI := T.topology
    ∃ (dD : T.SegmentProductDatum.{max uF uV, uF} n)
      (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hD : dD.IsLanglandsQuotient D),
      dD.multisegment = MoeglinWaldspurger.realize ρ x (MoeglinWaldspurger.dual a) ∧
      Aubert.adjustedOperator.{uF, uV} F T n
          (GeneralLinear.finiteLengthClass n F.Carrier A
            (hasFiniteLength_of_isIrreducible hA.2.2.1)) =
        GeneralLinear.finiteLengthClass n F.Carrier D
          (hasFiniteLength_of_isIrreducible hD.2.2.1) := by
  let := T.topology
  have hdeg : (MoeglinWaldspurger.realize ρ x (MoeglinWaldspurger.dual a)).degree = n := by
    rw [MoeglinWaldspurger.realize_degree_eq_of_support_eq ρ x
      (MoeglinWaldspurger.supportPreservation (a := a)), ← hdA]
    exact dA.multisegment_degree
  obtain ⟨dD, D, hdD, hD⟩ := exists_isLanglandsHead F T _ hdeg
  have hAhead : (MoeglinWaldspurger.realize ρ x a).IsLanglandsHead A := by
    rw [← hdA]
    exact isLanglandsHead_of_isLanglandsQuotient F T dA A hA
  refine ⟨dD, D, hD.isLanglandsQuotient, hdD, ?_⟩
  exact hMW ρ x a n A D hAhead ⟨dD, hdD, hD⟩

/-- Equality of the exact classes of two irreducible representations gives an
isomorphism. -/
theorem nonempty_iso_of_class_eq {n : ℕ} :
    letI := T.topology
    ∀ (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible),
      GeneralLinear.finiteLengthClass n F.Carrier π (hasFiniteLength_of_isIrreducible hπ) =
        GeneralLinear.finiteLengthClass n F.Carrier π' (hasFiniteLength_of_isIrreducible hπ') →
      Nonempty (π ≅ π') := by
  let := T.topology
  intro π π' hπ hπ' h
  obtain ⟨e⟩ := (ofRepresentation_eq_irreducible_iff π π' (hasFiniteLength_of_isIrreducible hπ)
    hπ' (hasFiniteLength_of_isIrreducible hπ')).mp h
  exact ⟨mkIso e⟩

/-- The closing step: if the adjusted dual of `C` has a label rank-lower than
the two column rectangles, the label of `C` has segments of length at most `l`. -/
theorem lengths_le_of_adjusted_rankLE
    (hMW : MoeglinWaldspurger.AubertCorrectness.{uF, max uF uV} F T)
    (ρ : T.CuspidalDatum.{max uF uV, uF}) (k l : ℕ) (hl : 0 < l) (hk : 2 ≤ k) {n : ℕ}
    (dC dCD : T.SegmentProductDatum.{max uF uV, uF} n) :
    letI := T.topology
    ∀ (C CD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hC : dC.IsLanglandsQuotient C) (hCD : dCD.IsLanglandsQuotient CD),
      Multisegment.RankLE dCD.multisegment
        (tadicMultisegment ρ l (k + 1) (by omega) + tadicMultisegment ρ l (k - 1) (by omega)) →
      Aubert.adjustedOperator.{uF, uV} F T n
          (GeneralLinear.finiteLengthClass n F.Carrier C
            (hasFiniteLength_of_isIrreducible hC.2.2.1)) =
        GeneralLinear.finiteLengthClass n F.Carrier CD
          (hasFiniteLength_of_isIrreducible hCD.2.2.1) →
      ∀ Δ ∈ dC.multisegment, Δ.length ≤ l := by
  let := T.topology
  intro C CD hC hCD hrank hdual
  obtain ⟨dE, E, hE, hdE, hDE⟩ := exists_adjusted_realize_dual F T hMW ρ
    (((k : ℝ) - l - 1) / 2) (MoeglinWaldspurger.neighborIntegerModel ρ l k hk hrank) dCD CD
    (MoeglinWaldspurger.realize_neighborIntegerModel ρ l k hk hrank).symm hCD
  have hCE : GeneralLinear.finiteLengthClass n F.Carrier C
        (hasFiniteLength_of_isIrreducible hC.2.2.1) =
      GeneralLinear.finiteLengthClass n F.Carrier E
        (hasFiniteLength_of_isIrreducible hE.2.2.1) := by
    rw [← hDE, ← hdual]
    exact (Aubert.adjustedOperator_involutive.{uF, uV} F T n _).symm
  obtain ⟨e⟩ := nonempty_iso_of_class_eq F T C E hC.2.2.1 hE.2.2.1 hCE
  have hlabel : dC.multisegment = dE.multisegment :=
    (orderedMultisegmentHeadClassification.{uF, uV} F T n dC dE C E hC hE).mpr ⟨e⟩
  rw [hlabel, hdE]
  exact MoeglinWaldspurger.realized_dual_lengths_le_neighborIntegerModel
    MoeglinWaldspurger.endingBound ρ l k hl hk hrank

/-- The neighboring-rectangle constituent length bound, conditional on the
actual Aubert correctness of the MW algorithm and on the head-product leading
term statement. -/
theorem neighborRectangleConstituentLengthBound_of_aubertCorrectness
    (hMW : MoeglinWaldspurger.AubertCorrectness.{uF, max uF uV} F T)
    (hH : Aubert.HeadProductLeadingTermStatement.{uF, uV} F T) :
    NeighborRectangleConstituentLengthBound.{uF, uV} F T := by
  let := T.topology
  intro ρ k l hl hk m n dA dB hdA hdB A B hA hB dC C hC hsub
  have hk1 : 0 < k + 1 := Nat.succ_pos k
  have hk2 : 0 < k - 1 := by omega
  have hxA : -((k : ℝ) + l - 1) / 2 + ((0 : ℤ) : ℝ) =
      -(((k + 1 : ℕ) : ℝ) + l - 2) / 2 := by
    push_cast
    ring
  have hxB : -((k : ℝ) + l - 1) / 2 + ((1 : ℤ) : ℝ) =
      -(((k - 1 : ℕ) : ℝ) + l - 2) / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  have hrA : MoeglinWaldspurger.realize ρ (-((k : ℝ) + l - 1) / 2)
      (MoeglinWaldspurger.rectangle 0 (k + 1 - 1) (l - 1)) =
        tadicMultisegment ρ (k + 1) l hl :=
    realize_rectangle_tadic F T ρ 0 (k + 1) l hk1 hl _ hxA
  have hrB : MoeglinWaldspurger.realize ρ (-((k : ℝ) + l - 1) / 2)
      (MoeglinWaldspurger.rectangle 1 (k - 1 - 1) (l - 1)) =
        tadicMultisegment ρ (k - 1) l hl :=
    realize_rectangle_tadic F T ρ 1 (k - 1) l hk2 hl _ hxB
  have hrAD : MoeglinWaldspurger.realize ρ (-((k : ℝ) + l - 1) / 2)
      (MoeglinWaldspurger.dual (MoeglinWaldspurger.rectangle 0 (k + 1 - 1) (l - 1))) =
        tadicMultisegment ρ l (k + 1) hk1 :=
    realize_dual_rectangle_tadic F T ρ 0 (k + 1) l hk1 hl _ hxA
  have hrBD : MoeglinWaldspurger.realize ρ (-((k : ℝ) + l - 1) / 2)
      (MoeglinWaldspurger.dual (MoeglinWaldspurger.rectangle 1 (k - 1 - 1) (l - 1))) =
        tadicMultisegment ρ l (k - 1) hk2 :=
    realize_dual_rectangle_tadic F T ρ 1 (k - 1) l hk2 hl _ hxB
  obtain ⟨dAD, AD, hAD, hdAD, hDA⟩ := exists_adjusted_realize_dual F T hMW ρ
    (-((k : ℝ) + l - 1) / 2) (MoeglinWaldspurger.rectangle 0 (k + 1 - 1) (l - 1)) dA A
    (hdA.trans hrA.symm) hA
  obtain ⟨dBD, BD, hBD, hdBD, hDB⟩ := exists_adjusted_realize_dual F T hMW ρ
    (-((k : ℝ) + l - 1) / 2) (MoeglinWaldspurger.rectangle 1 (k - 1 - 1) (l - 1)) dB B
    (hdB.trans hrB.symm) hB
  obtain ⟨CD, hCDirr, hDC, hsubD⟩ :=
    Aubert.AdjustedProductConstituents.exists_adjusted_isSubquotient F T A AD B BD C
      hA.2.2.1 hAD.2.2.1 hB.2.2.1 hBD.2.2.1 hC.2.2.1 hDA hDB hsub
  obtain ⟨dCD, hCD⟩ := exists_weakHead F T CD hCDirr
  have hrank := (hH m n dAD dBD dCD AD BD CD hAD hBD hCD).1 hsubD
  rw [hdAD.trans hrAD, hdBD.trans hrBD] at hrank
  exact lengths_le_of_adjusted_rankLE F T hMW ρ k l hl hk dC dCD C CD hC hCD hrank hDC

end Langlands.Classification.SpehNeighborProduct
