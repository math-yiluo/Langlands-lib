import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.BigOperators.Fin

/-! Ordered enumeration and actual segment constituent data for every multisegment. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Choose a maximal beginning for the integral-twist preorder at each step.
The order ignores segment lengths and therefore also handles repeated segments. -/
private theorem exists_precedenceOrderedList (a : T.Multisegment.{uV, uF}) :
    ∃ l : List (T.Segment.{uV, uF}), (l : Multiset _) = a ∧
      T.IsPrecedenceOrderedList l := by
  classical
  let : Preorder (T.Segment.{uV, uF}) := {
    le Δ Γ := ∃ k : ℕ, Γ.base = Δ.base.twist (k : ℝ)
    le_refl Δ := ⟨0, by simp⟩
    le_trans Δ Γ Θ := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨j + i, ?_⟩
      rw [hj, hi, CuspidalDatum.twist_twist, Nat.cast_add]
  }
  have hnot : ∀ Δ Γ : T.Segment.{uV, uF}, Γ ≤ Δ → ¬ Δ.Precedes Γ := by
    intro Δ Γ hback hprec
    obtain ⟨i, hi, hfor⟩ := hprec.2
    obtain ⟨j, hj⟩ := hback
    rw [hfor, CuspidalDatum.twist_twist] at hj
    have hz : (j : ℤ) + (i : ℤ) = 0 :=
      (cuspidalIntegralTwistFreeness.{uF, uV} F T Δ.base ((j : ℤ) + (i : ℤ))).mp
        (by simpa only [Int.cast_add, Int.cast_natCast] using hj.symm)
    omega
  induction a using Multiset.strongInductionOn with
  | ih a ih =>
    by_cases ha : a = 0
    · subst a
      exact ⟨[], rfl, List.Pairwise.nil⟩
    have hne : a.toFinset.Nonempty := by
      obtain ⟨Δ, hΔ⟩ := Multiset.exists_mem_of_ne_zero ha
      exact ⟨Δ, Multiset.mem_toFinset.mpr hΔ⟩
    obtain ⟨Δ, hΔ, hmax⟩ := Finset.exists_maximal hne
    have hmem : Δ ∈ a := Multiset.mem_toFinset.mp hΔ
    obtain ⟨l, hl, hord⟩ := ih (a.erase Δ) (Multiset.erase_lt.mpr hmem)
    refine ⟨Δ :: l, ?_, ?_⟩
    · change Δ ::ₘ (l : Multiset _) = a
      rw [hl]
      exact Multiset.cons_erase hmem
    · apply List.pairwise_cons.mpr
      refine ⟨?_, hord⟩
      intro Γ hΓ hprec
      have hΓerase : Γ ∈ a.erase Δ := by
        rw [← hl]
        exact hΓ
      have hΓmem : Γ ∈ a.toFinset :=
        Multiset.mem_toFinset.mpr (Multiset.mem_of_mem_erase hΓerase)
      have hle : Δ ≤ Γ := by
        obtain ⟨k, _, hk⟩ := hprec.2
        exact ⟨k, hk⟩
      exact hnot Δ Γ (hmax hΓmem hle) hprec

/-- Every multisegment has a nonprecedence enumeration with its total degree. -/
theorem multisegmentNonprecedenceEnumeration :
    MultisegmentNonprecedenceEnumeration.{uF, uV} F T := by
  intro a
  obtain ⟨l, hl, hord⟩ := exists_precedenceOrderedList F T a
  refine ⟨l.length, l.get, ?_, ?_, ?_⟩
  · simpa only [Multisegment.IsOrdering, List.ofFn_get] using hl
  · apply (T.isPrecedenceOrdered_iff_list l.get).mpr
    simpa only [List.ofFn_get] using hord
  · have hsum := congrArg Multisegment.degree hl
    calc
      ∑ i, (l.get i).degree = (l.map Segment.degree).sum := by
        rw [← List.sum_ofFn]
        change (List.ofFn (Segment.degree ∘ l.get)).sum = _
        rw [← List.map_ofFn, List.ofFn_get]
      _ = a.degree := by
        simpa only [Multisegment.degree, Multiset.map_coe, Multiset.sum_coe] using hsum

/-- Every multisegment admits ordered actual segment-socle data and ordered
actual segment-head data, including the empty multisegment. -/
theorem multisegmentConstituentDataExistence :
    MultisegmentConstituentDataExistence.{uF, uV} F T := by
  classical
  let := T.topology
  intro a
  obtain ⟨r, Δ, hΔ, hord, hsum⟩ :=
    multisegmentNonprecedenceEnumeration.{uF, uV} F T a
  constructor
  · have hex : ∀ i : Fin r,
        ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ i).degree F.Carrier),
          T.IsSegmentSocle (Δ i) π := by
      intro i
      obtain ⟨π, hπ, _⟩ := segmentZelevinskyConstituentExistence.{uF, max uF uV} F T (Δ i)
      exact ⟨π, hπ⟩
    choose π hπ using hex
    exact ⟨⟨r, Δ, hsum, π⟩, hΔ, hord, hπ⟩
  · have hex : ∀ i : Fin r,
        ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ i).degree F.Carrier),
          T.IsSegmentHead (Δ i) π := by
      intro i
      obtain ⟨π, hπ, _⟩ := segmentSpecialConstituentExistence.{uF, max uF uV} F T (Δ i)
      exact ⟨π, hπ⟩
    choose π hπ using hex
    exact ⟨⟨r, Δ, hsum, π⟩, hΔ, hord, hπ⟩

end Langlands.Classification
