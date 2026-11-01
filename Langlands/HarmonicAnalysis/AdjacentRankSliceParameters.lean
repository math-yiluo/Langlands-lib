import Langlands.HarmonicAnalysis.AdjacentRankAffineFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAffineParameters
import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.Group.GL.Maps

/-! Exact product parameters for both anti-triangular slices. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

open GeneralLinear

universe uK

private def adjacentRightEntryIndex (n : ℕ) (p : UpperEntryPair (n + 1)) :
    RectangularFreeEntry (adjacentRankRightColumns n) :=
  ⟨p.1.1.rev, ⟨p.1.2, by
    simp only [adjacentRankRightColumns, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_rev]
    have hp : p.1.1.val < p.1.2.val := p.2
    have hi := p.1.1.isLt
    omega⟩⟩

private theorem adjacentRightEntryIndex_bijective (n : ℕ) :
    Function.Bijective (adjacentRightEntryIndex n) := by
  constructor
  · intro p q h
    have hr := congrArg (fun a : RectangularFreeEntry (adjacentRankRightColumns n) => a.1) h
    have hc := congrArg (fun a : RectangularFreeEntry (adjacentRankRightColumns n) => a.2.1) h
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.rev_injective hr
    · exact hc
  · rintro ⟨i, j, hj⟩
    have hs : n < i.val + j.val := by
      simpa only [adjacentRankRightColumns, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hp : i.rev < j := by
      change i.rev.val < j.val
      simp only [Fin.val_rev]
      have hi := i.isLt
      omega
    refine ⟨⟨(i.rev, j), hp⟩, ?_⟩
    have hr : (adjacentRightEntryIndex n ⟨(i.rev, j), hp⟩).1 = i := Fin.rev_rev i
    apply Sigma.ext hr
    apply (Subtype.heq_iff_coe_eq (by intro x; rw [hr])).mpr
    rfl

/-- Reversal of the row sends strict upper entries to the right free slice. -/
def adjacentRankRightEntryEquiv (n : ℕ) : UpperEntryPair (n + 1) ≃
    RectangularFreeEntry (adjacentRankRightColumns n) :=
  Equiv.ofBijective (adjacentRightEntryIndex n) (adjacentRightEntryIndex_bijective n)

/-- Reverse a positive column, retaining its range in the positive columns. -/
def adjacentRankReversedColumn {n : ℕ} (p : UpperEntryPair (n + 1)) : Fin (n + 1) :=
  ⟨n + 1 - p.1.2.val, by
    have hp : p.1.1.val < p.1.2.val := p.2
    have hj : p.1.2.val < n + 1 := p.1.2.isLt
    omega⟩

private def adjacentLeftEntryIndex (n : ℕ) : UpperEntryPair (n + 1) ⊕ Fin (n + 1) →
    RectangularFreeEntry (fun i => (adjacentRankRightColumns n i)ᶜ)
  | .inl p => ⟨p.1.1, ⟨adjacentRankReversedColumn p, by
      simp only [Finset.mem_compl, adjacentRankRightColumns, Finset.mem_filter,
        Finset.mem_univ, true_and]
      change ¬ n < p.1.1.val + (n + 1 - p.1.2.val)
      have hp : p.1.1.val < p.1.2.val := p.2
      have hj : p.1.2.val < n + 1 := p.1.2.isLt
      omega⟩⟩
  | .inr i => ⟨i, ⟨0, by
      simp only [Finset.mem_compl, adjacentRankRightColumns, Finset.mem_filter,
        Finset.mem_univ, true_and, Fin.val_zero, add_zero]
      have hi := i.isLt
      omega⟩⟩

private theorem adjacentLeftEntryIndex_injective (n : ℕ) :
    Function.Injective (adjacentLeftEntryIndex n) := by
  intro x y h
  have hr := congrArg (fun a : RectangularFreeEntry
    (fun i => (adjacentRankRightColumns n i)ᶜ) => a.1.val) h
  have hc := congrArg (fun a : RectangularFreeEntry
    (fun i => (adjacentRankRightColumns n i)ᶜ) => a.2.1.val) h
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.ext hr
      · apply Fin.ext
        change n + 1 - p.1.2.val = n + 1 - q.1.2.val at hc
        have hp : p.1.2.val < n + 1 := p.1.2.isLt
        have hq : q.1.2.val < n + 1 := q.1.2.isLt
        omega
    | inr i =>
      change n + 1 - p.1.2.val = 0 at hc
      have hp : p.1.2.val < n + 1 := p.1.2.isLt
      omega
  | inr i =>
    cases y with
    | inl p =>
      change 0 = n + 1 - p.1.2.val at hc
      have hp : p.1.2.val < n + 1 := p.1.2.isLt
      omega
    | inr j => exact congrArg Sum.inr (Fin.ext hr)

private theorem adjacentLeftEntryIndex_surjective (n : ℕ) :
    Function.Surjective (adjacentLeftEntryIndex n) := by
  rintro ⟨i, j, hj⟩
  have hs : ¬ n < i.val + j.val := by
    simpa only [Finset.mem_compl, adjacentRankRightColumns, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj
  by_cases hz : j = 0
  · subst j
    exact ⟨.inr i, rfl⟩
  · have hjp : 0 < j.val := by exact Fin.pos_of_ne_zero hz
    let k : Fin (n + 1) := ⟨n + 1 - j.val, by
      have hj := j.isLt
      omega⟩
    have hp : i < k := by
      change i.val < n + 1 - j.val
      have hj := j.isLt
      omega
    refine ⟨.inl ⟨(i, k), hp⟩, ?_⟩
    apply Sigma.ext (show i = i from rfl)
    apply heq_of_eq
    apply Subtype.ext
    apply Fin.ext
    change n + 1 - (n + 1 - j.val) = j.val
    have hj := j.isLt
    omega

/-- The left free entries are the reversed strict upper entries and a whole row. -/
def adjacentRankLeftEntryEquiv (n : ℕ) : UpperEntryPair (n + 1) ⊕ Fin (n + 1) ≃
    RectangularFreeEntry (fun i => (adjacentRankRightColumns n i)ᶜ) :=
  Equiv.ofBijective (adjacentLeftEntryIndex n)
    ⟨adjacentLeftEntryIndex_injective n, adjacentLeftEntryIndex_surjective n⟩

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- Parametrize the right slice by its original strict upper coordinates. -/
def adjacentRankRightParam (n : ℕ) (X : UpperEntryPair (n + 1) → K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  rectangularSliceParam (adjacentRankRightColumns n) (adjacentRankAntidiagonal n)
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (adjacentRankRightEntryEquiv n)) X)

/-- Parametrize the left slice; both strict upper and row entries are negated. -/
def adjacentRankLeftParam (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × (Fin (n + 1) → K)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  rectangularSliceParam (fun i => (adjacentRankRightColumns n i)ᶜ)
    (adjacentRankShiftedAntidiagonal n)
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (adjacentRankLeftEntryEquiv n))
      ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : UpperEntryPair (n + 1) ⊕ Fin (n + 1) => K)).symm (-z.1, -z.2)))

omit [IsTopologicalRing K] [BorelSpace K] [SecondCountableTopology K] in
/-- Right-slice coordinates push forward the supplied strict-upper product exactly. -/
theorem adjacentRankRightParam_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving (adjacentRankRightParam n) (upperEntryProductMeasure ν (n + 1))
      (adjacentRankRightSliceMeasure ν n) := by
  have hindex := measurePreserving_piCongrLeft
    (α := fun _ : RectangularFreeEntry (adjacentRankRightColumns n) => K)
    (fun _ => ν.measure) (adjacentRankRightEntryEquiv n)
  exact (rectangularSliceParam_preserving ν (adjacentRankRightColumns n)
    (adjacentRankAntidiagonal n)).comp hindex

/-- Left-slice coordinates push forward the exact product, including all negations. -/
theorem adjacentRankLeftParam_preserving [LocallyCompactSpace K] [T2Space K] (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving (adjacentRankLeftParam n)
      ((upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν (n + 1)))
      (adjacentRankLeftSliceMeasure ν n) := by
  have hnscalar : MeasurePreserving (fun x : K => -x) ν.measure ν.measure :=
    measurePreserving_neg ν.measure
  have hncoord : MeasurePreserving (fun X : UpperEntryPair (n + 1) → K => -X)
      (upperEntryProductMeasure ν (n + 1)) (upperEntryProductMeasure ν (n + 1)) :=
    measurePreserving_pi (fun _ => ν.measure) (fun _ => ν.measure) (fun _ => hnscalar)
  have hnrow : MeasurePreserving (fun y : Fin (n + 1) → K => -y)
      (rowMeasure ν (n + 1)) (rowMeasure ν (n + 1)) :=
    measurePreserving_pi (fun _ => ν.measure) (fun _ => ν.measure) (fun _ => hnscalar)
  have hsum := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : UpperEntryPair (n + 1) ⊕ Fin (n + 1) => ν.measure)
  have hindex := measurePreserving_piCongrLeft
    (α := fun _ : RectangularFreeEntry (fun i => (adjacentRankRightColumns n i)ᶜ) => K)
    (fun _ => ν.measure) (adjacentRankLeftEntryEquiv n)
  exact (rectangularSliceParam_preserving ν (fun i => (adjacentRankRightColumns n i)ᶜ)
    (adjacentRankShiftedAntidiagonal n)).comp
      (hindex.comp (hsum.comp (hncoord.prod hnrow)))

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K]
  [SecondCountableTopology K] in
@[simp] theorem adjacentRankRightParam_upper (n : ℕ) (X : UpperEntryPair (n + 1) → K)
    (p : UpperEntryPair (n + 1)) :
    adjacentRankRightParam n X p.1.1.rev p.1.2 = X p := by
  change (if h : (adjacentRightEntryIndex n p).2.1 ∈
      adjacentRankRightColumns n (adjacentRightEntryIndex n p).1 then
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (adjacentRankRightEntryEquiv n)) X)
      ⟨(adjacentRightEntryIndex n p).1, ⟨(adjacentRightEntryIndex n p).2.1, h⟩⟩
    else adjacentRankAntidiagonal n (adjacentRightEntryIndex n p).1
      (adjacentRightEntryIndex n p).2.1) = _
  rw [dite_eq_left (adjacentRightEntryIndex n p).2.2]
  change ((MeasurableEquiv.piCongrLeft (fun _ => K) (adjacentRankRightEntryEquiv n)) X)
    (adjacentRankRightEntryEquiv n p) = _
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K]
  [SecondCountableTopology K] in
private theorem adjacentRankLeftParam_selected (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × (Fin (n + 1) → K))
    (o : UpperEntryPair (n + 1) ⊕ Fin (n + 1)) :
    adjacentRankLeftParam n z (adjacentLeftEntryIndex n o).1
      (adjacentLeftEntryIndex n o).2.1 = o.elim (fun p => -z.1 p) (fun i => -z.2 i) := by
  change (if h : (adjacentLeftEntryIndex n o).2.1 ∈
      (adjacentRankRightColumns n (adjacentLeftEntryIndex n o).1)ᶜ then
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (adjacentRankLeftEntryEquiv n))
      ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : UpperEntryPair (n + 1) ⊕ Fin (n + 1) => K)).symm (-z.1, -z.2)))
      ⟨(adjacentLeftEntryIndex n o).1, ⟨(adjacentLeftEntryIndex n o).2.1, h⟩⟩
    else adjacentRankShiftedAntidiagonal n (adjacentLeftEntryIndex n o).1
      (adjacentLeftEntryIndex n o).2.1) = _
  rw [dite_eq_left (adjacentLeftEntryIndex n o).2.2]
  change ((MeasurableEquiv.piCongrLeft (fun _ => K) (adjacentRankLeftEntryEquiv n))
      ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : UpperEntryPair (n + 1) ⊕ Fin (n + 1) => K)).symm (-z.1, -z.2)))
    (adjacentRankLeftEntryEquiv n o) = _
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  cases o <;> rfl

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K]
  [SecondCountableTopology K] in
@[simp] theorem adjacentRankLeftParam_upper (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × (Fin (n + 1) → K)) (p : UpperEntryPair (n + 1)) :
    adjacentRankLeftParam n z p.1.1 (adjacentRankReversedColumn p) = -z.1 p :=
  adjacentRankLeftParam_selected n z (.inl p)

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K]
  [SecondCountableTopology K] in
@[simp] theorem adjacentRankLeftParam_zero (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × (Fin (n + 1) → K)) (i : Fin (n + 1)) :
    adjacentRankLeftParam n z i 0 = -z.2 i :=
  adjacentRankLeftParam_selected n z (.inr i)

omit [BorelSpace K] [SecondCountableTopology K] in
/-- The right parameter is the actual Weyl times upper-unipotent product. -/
theorem adjacentRankRightParam_eq_weyl (n : ℕ) (u : upperUnipotent (n + 1) K) :
    adjacentRankRightParam n (upperEntryCoordinates (n + 1) u) =
      (weylLong (n + 1) K).val * u.val.val := by
  ext i j
  change _ = (weylLong (n + 1) K * u.val) i j
  rw [weylLong_mul_entry]
  by_cases hij : i.rev < j
  · have hp := adjacentRankRightParam_upper n (upperEntryCoordinates (n + 1) u)
      ⟨(i.rev, j), hij⟩
    simpa only [Fin.rev_rev, upperEntryCoordinates_apply] using hp
  · have hm : j ∉ adjacentRankRightColumns n i := by
      simp only [adjacentRankRightColumns, Finset.mem_filter, Finset.mem_univ, true_and]
      change ¬ i.rev.val < j.val at hij
      simp only [Fin.val_rev] at hij
      have hi := i.isLt
      omega
    change (if h : j ∈ adjacentRankRightColumns n i then _
      else adjacentRankAntidiagonal n i j) = _
    rw [dite_eq_right hm]
    by_cases he : i.rev = j
    · rw [← he, UpperUnipotent.entry_diag]
      have hv : i.val + i.rev.val = n := by
        simp only [Fin.val_rev]
        have hi := i.isLt
        omega
      change (if i.val + i.rev.val = n then 1 else 0) = 1
      exact ite_eq_left hv
    · have hji : j < i.rev := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm he)
      rw [UpperUnipotent.entry_eq_zero u hji]
      have hv : i.val + j.val ≠ n := by
        intro hv
        apply he
        apply Fin.ext
        simp only [Fin.val_rev]
        have hi := i.isLt
        omega
      exact ite_eq_right hv

omit [BorelSpace K] [SecondCountableTopology K] in
/-- The left parameter has first column minus the free row and reversed remaining
columns of the upper unipotent, with the literal negative signs. -/
theorem adjacentRankLeftParam_eq_columns (n : ℕ) (u : upperUnipotent (n + 1) K)
    (y : Fin (n + 1) → K) :
    adjacentRankLeftParam n (upperEntryCoordinates (n + 1) u, y) =
      fun i j => Fin.cases (-y i) (fun k : Fin n => -u.val.val i k.rev.succ) j := by
  ext i j
  induction j using Fin.cases with
  | zero => exact adjacentRankLeftParam_zero n _ i
  | succ k =>
    simp only [Fin.cases_succ]
    by_cases hik : i < k.rev.succ
    · let p : UpperEntryPair (n + 1) := ⟨(i, k.rev.succ), hik⟩
      have hc : adjacentRankReversedColumn p = k.succ := by
        apply Fin.ext
        change n + 1 - (k.rev.val + 1) = k.val + 1
        simp only [Fin.val_rev]
        have hk := k.isLt
        omega
      have hp := adjacentRankLeftParam_upper n (upperEntryCoordinates (n + 1) u, y) p
      rw [hc] at hp
      simpa only [upperEntryCoordinates_apply] using hp
    · have hm : k.succ ∉ (adjacentRankRightColumns n i)ᶜ := by
        simp only [Finset.mem_compl, adjacentRankRightColumns, Finset.mem_filter,
          Finset.mem_univ, true_and, not_not]
        change ¬ i.val < k.rev.val + 1 at hik
        simp only [Fin.val_rev] at hik
        simp only [Fin.val_succ]
        have hk := k.isLt
        omega
      change (if h : k.succ ∈ (adjacentRankRightColumns n i)ᶜ then _
        else adjacentRankShiftedAntidiagonal n i k.succ) = _
      rw [dite_eq_right hm]
      by_cases he : i = k.rev.succ
      · rw [he, UpperUnipotent.entry_diag]
        have hv : k.rev.succ.val + k.succ.val = n + 1 := by
          simp only [Fin.val_succ, Fin.val_rev]
          have hk := k.isLt
          omega
        exact ite_eq_left hv
      · have hki : k.rev.succ < i := lt_of_le_of_ne (le_of_not_gt hik) (Ne.symm he)
        rw [UpperUnipotent.entry_eq_zero u hki, neg_zero]
        have hv : i.val + k.succ.val ≠ n + 1 := by
          intro hv
          apply he
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_rev] at *
          have hk := k.isLt
          omega
        exact ite_eq_right hv

end Langlands.HarmonicAnalysis
