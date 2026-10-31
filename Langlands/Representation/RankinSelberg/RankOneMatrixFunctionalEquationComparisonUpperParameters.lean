import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAffineParameters
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonTriangularFourier
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-! Actual upper-unipotent and first-column parameters for the upper affine slice. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

open GeneralLinear

universe uK

private def upperEntryIndex (n : ℕ) : UpperEntryPair (n + 1) ⊕ Fin n →
    RectangularFreeEntry (fun i => (shiftedLowerSliceColumns n i)ᶜ)
  | .inl p => ⟨p.1.1, ⟨p.1.2, by
      apply Finset.mem_compl.mpr
      simp only [shiftedLowerSliceColumns, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro (⟨hz, _⟩ | ⟨_, hle⟩)
      · have hp : p.1.1.val < p.1.2.val := p.2
        simp only [hz, Fin.val_zero] at hp
        omega
      · exact (not_le_of_gt p.2) hle⟩⟩
  | .inr k => ⟨k.castSucc, ⟨0, by
      simp [shiftedLowerSliceColumns, Fin.castSucc_ne_last k]⟩⟩

private theorem upperEntryIndex_injective (n : ℕ) : Function.Injective (upperEntryIndex n) := by
  intro x y h
  have hr := congrArg (fun q : RectangularFreeEntry (fun i => (shiftedLowerSliceColumns n i)ᶜ) =>
    q.1.val) h
  have hc := congrArg (fun q : RectangularFreeEntry (fun i => (shiftedLowerSliceColumns n i)ᶜ) =>
    q.2.1.val) h
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      apply congrArg Sum.inl
      exact Subtype.ext (Prod.ext (Fin.ext hr) (Fin.ext hc))
    | inr k =>
      change p.1.2.val = 0 at hc
      have hp : p.1.1.val < p.1.2.val := p.2
      omega
  | inr k =>
    cases y with
    | inl p =>
      change 0 = p.1.2.val at hc
      have hp : p.1.1.val < p.1.2.val := p.2
      omega
    | inr l =>
      apply congrArg Sum.inr
      exact Fin.ext hr

private theorem upperEntryIndex_surjective (n : ℕ) : Function.Surjective (upperEntryIndex n) := by
  intro q
  obtain ⟨i, j, hj⟩ := q
  have hnot : ¬((j = 0 ∧ i = Fin.last n) ∨ (0 < j ∧ j ≤ i)) := by
    simpa only [Finset.mem_compl, shiftedLowerSliceColumns, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj
  by_cases hz : j = 0
  · have hi : i ≠ Fin.last n := fun he => hnot (Or.inl ⟨hz, he⟩)
    obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    subst j
    exact ⟨.inr k, rfl⟩
  · have hij : i < j := lt_of_not_ge fun hle =>
      hnot (Or.inr ⟨Fin.pos_of_ne_zero hz, hle⟩)
    exact ⟨.inl ⟨(i, j), hij⟩, rfl⟩

/-- The upper free entries consist of all strict-upper entries and the first
column except its final entry. -/
def upperFirstColumnEntryEquiv (n : ℕ) : UpperEntryPair (n + 1) ⊕ Fin n ≃
    RectangularFreeEntry (fun i => (shiftedLowerSliceColumns n i)ᶜ) :=
  Equiv.ofBijective (upperEntryIndex n)
    ⟨upperEntryIndex_injective n, upperEntryIndex_surjective n⟩

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- Fill the upper affine slice from independent strict-upper entries and first
column entries, keeping the supplied trailing diagonal fixed at one. -/
def upperFreeParam (n : ℕ) (z : (UpperEntryPair (n + 1) → K) × (Fin n → K)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  rectangularSliceParam (fun i => (shiftedLowerSliceColumns n i)ᶜ) (trailingIdentity n)
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (upperFirstColumnEntryEquiv n))
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : UpperEntryPair (n + 1) ⊕ Fin n => K)).symm z))

omit [IsTopologicalRing K] [BorelSpace K] [SecondCountableTopology K] in
/-- Independent upper entries and first-column entries carry exactly the actual
upper affine slice measure, with no scalar discrepancy. -/
theorem upperFreeParam_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving (upperFreeParam n)
      ((upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν n))
      (upperFirstColumnSliceMeasure ν n) := by
  have hsum := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : UpperEntryPair (n + 1) ⊕ Fin n => ν.measure)
  have hindex := measurePreserving_piCongrLeft
    (α := fun _ : RectangularFreeEntry (fun i => (shiftedLowerSliceColumns n i)ᶜ) => K)
    (fun _ => ν.measure) (upperFirstColumnEntryEquiv n)
  exact (rectangularSliceParam_preserving ν (fun i => (shiftedLowerSliceColumns n i)ᶜ)
    (trailingIdentity n)).comp (hindex.comp hsum)

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K] [SecondCountableTopology K] in
private theorem upperParam_selected (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × (Fin n → K))
    (o : UpperEntryPair (n + 1) ⊕ Fin n) :
    upperFreeParam n z (upperEntryIndex n o).1 (upperEntryIndex n o).2.1 =
      o.elim z.1 z.2 := by
  change (if h : (upperEntryIndex n o).2.1 ∈ (shiftedLowerSliceColumns n (upperEntryIndex n o).1)ᶜ then
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (upperFirstColumnEntryEquiv n))
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : UpperEntryPair (n + 1) ⊕ Fin n => K)).symm z))
        ⟨(upperEntryIndex n o).1, ⟨(upperEntryIndex n o).2.1, h⟩⟩
    else trailingIdentity n (upperEntryIndex n o).1 (upperEntryIndex n o).2.1) = _
  rw [dite_eq_left (upperEntryIndex n o).2.2]
  have hi : (⟨(upperEntryIndex n o).1, ⟨(upperEntryIndex n o).2.1, (upperEntryIndex n o).2.2⟩⟩ :
      RectangularFreeEntry (fun i => (shiftedLowerSliceColumns n i)ᶜ)) =
        upperFirstColumnEntryEquiv n o := rfl
  rw [hi]
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  cases o <;> rfl

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K] [SecondCountableTopology K] in
@[simp] theorem upperFreeParam_upperEntry (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × (Fin n → K)) (p : UpperEntryPair (n + 1)) :
    upperFreeParam n z p.1.1 p.1.2 = z.1 p :=
  upperParam_selected n z (.inl p)

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K] [SecondCountableTopology K] in
@[simp] theorem upperFreeParam_firstColumn (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × (Fin n → K)) (i : Fin n) :
    upperFreeParam n z i.castSucc 0 = z.2 i := upperParam_selected n z (.inr i)

/-- The triangular first-column action of the upper unipotent with scalar entries X. -/
def upperColumnAction {n : ℕ} (X : UpperEntryPair (n + 1) → K) (v : Fin n → K) : Fin n → K :=
  fun i => v i + ∑ j : {j : Fin n // i < j},
    X ⟨(i.castSucc, j.val.castSucc), by exact j.2⟩ * v j

omit [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
private theorem continuous_upperColumnAction (n : ℕ) :
    Continuous (fun z : (UpperEntryPair (n + 1) → K) × (Fin n → K) =>
      upperColumnAction z.1 z.2) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp continuous_snd).add <|
    continuous_finsetSum _ fun j _ =>
      ((continuous_apply (⟨(i.castSucc, j.val.castSucc), j.2⟩ : UpperEntryPair (n + 1))).comp
        continuous_fst).mul ((continuous_apply j.val).comp continuous_snd)

/-- For every fixed upper-entry family, the triangular first-column action
preserves the supplied row Haar measure. -/
theorem upperColumnAction_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {n : ℕ} (X : UpperEntryPair (n + 1) → K) :
    MeasurePreserving (upperColumnAction X) (rowMeasure ν n) (rowMeasure ν n) := by
  let f : (Fin n → K) → Fin n → K := fun v => upperColumnAction X v - v
  have hf : Continuous f :=
    ((continuous_upperColumnAction n).comp (continuous_const.prodMk continuous_id)).sub continuous_id
  have hdep (i : Fin n) (v w : Fin n → K)
      (h : ∀ j : Fin n, n - j.val < n - i.val → v j = w j) : f v i = f w i := by
    have hs : (∑ j : {j : Fin n // i < j},
        X ⟨(i.castSucc, j.val.castSucc), j.2⟩ * v j) =
      ∑ j : {j : Fin n // i < j}, X ⟨(i.castSucc, j.val.castSucc), j.2⟩ * w j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h j]
      have hj : i.val < j.val.val := j.2
      have hlt := j.val.isLt
      omega
    simp only [f, Pi.sub_apply, upperColumnAction]
    rw [hs]
    abel
  have hp := finiteTriangularTranslation (Fin n) (fun _ => K) (fun _ => ν.measure)
    (fun i => n - i.val) f hf.measurable hdep
  have he : (fun v i => f v i + v i) = upperColumnAction X := by
    funext v i
    exact sub_add_cancel _ _
  rw [he] at hp
  exact hp

/-- The first-column triangular action also preserves the joint product of
upper-entry coordinates and first-column coordinates. -/
theorem upperColumnAction_product_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving
      (fun z : (UpperEntryPair (n + 1) → K) × (Fin n → K) =>
        (z.1, upperColumnAction z.1 z.2))
      ((upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν n))
      ((upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν n)) := by
  exact (MeasurePreserving.id (upperEntryProductMeasure ν (n + 1))).skew_product
    (continuous_upperColumnAction n).measurable
    (Filter.Eventually.of_forall fun X => (upperColumnAction_preserving ν X).map_eq)

/-- The upper-unipotent column parameters carry exactly the upper affine slice measure. -/
theorem upperColumnParam_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving
      (fun z : (UpperEntryPair (n + 1) → K) × (Fin n → K) =>
        upperFreeParam n (z.1, upperColumnAction z.1 z.2))
      ((upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν n))
      (upperFirstColumnSliceMeasure ν n) :=
  (upperFreeParam_preserving ν n).comp (upperColumnAction_product_preserving ν n)

/-- The matrix with first column `(v,0)` and identity in the remaining columns. -/
def firstColumnMatrix (n : ℕ) (v : Fin n → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => if j = 0 then Fin.lastCases 0 v i else if i = j then 1 else 0

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K] in
private theorem mul_firstColumn_zero {n : ℕ} (u : upperUnipotent (n + 1) K)
    (v : Fin n → K) (i : Fin (n + 1)) :
    (u.val.val * firstColumnMatrix n v) i 0 =
      ∑ k : Fin n, u.val.val i k.castSucc * v k := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [firstColumnMatrix]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K] in
private theorem mul_firstColumn_last_zero {n : ℕ} (u : upperUnipotent (n + 1) K)
    (v : Fin n → K) : (u.val.val * firstColumnMatrix n v) (Fin.last n) 0 = 0 := by
  rw [mul_firstColumn_zero]
  apply Finset.sum_eq_zero
  intro k _
  rw [UpperUnipotent.entry_eq_zero u (Fin.castSucc_lt_last k), zero_mul]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K] in
private theorem mul_firstColumn_of_ne_zero {n : ℕ} (u : upperUnipotent (n + 1) K)
    (v : Fin n → K) (i j : Fin (n + 1)) (hj : j ≠ 0) :
    (u.val.val * firstColumnMatrix n v) i j = u.val.val i j := by
  simp [Matrix.mul_apply, firstColumnMatrix, hj]

private theorem sum_dite_zero {ι M : Type*} [Fintype ι] [AddCommMonoid M] (p : ι → Prop)
    [DecidablePred p] (f : ∀ i, p i → M) :
    ∑ i, (if h : p i then f i h else 0) = ∑ i : {i // p i}, f i i.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  rw [Finset.sum_eq_zero (s := Finset.univ) (fun (i : {i // ¬p i}) _ => dite_eq_right i.2),
    add_zero]
  exact Finset.sum_congr rfl fun i _ => dite_eq_left i.2

omit [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
private theorem mul_firstColumn_castSucc {n : ℕ} (u : upperUnipotent (n + 1) K)
    (v : Fin n → K) (i : Fin n) :
    (u.val.val * firstColumnMatrix n v) i.castSucc 0 =
      upperColumnAction (upperEntryCoordinates (n + 1) u) v i := by
  have ht (j : Fin n) : u.val.val i.castSucc j.castSucc * v j =
      (if j = i then v i else 0) +
        (if h : i < j then
          upperEntryCoordinates (n + 1) u ⟨(i.castSucc, j.castSucc), h⟩ * v j else 0) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [upperEntryCoordinates_apply, hij, hij.ne']
    · simp [UpperUnipotent.entry_diag]
    · rw [UpperUnipotent.entry_eq_zero u hji]
      simp [hji.ne, not_lt_of_ge hji.le]
  rw [mul_firstColumn_zero]
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum_dite_zero]
  rfl

omit [BorelSpace K] [SecondCountableTopology K] in
/-- The triangular upper parameters are the actual product of the upper
unipotent and the matrix with prescribed first column and trailing identity. -/
theorem upperColumnParam_eq_mul (n : ℕ) (u : upperUnipotent (n + 1) K) (v : Fin n → K) :
    upperFreeParam n (upperEntryCoordinates (n + 1) u,
      upperColumnAction (upperEntryCoordinates (n + 1) u) v) =
      u.val.val * firstColumnMatrix n v := by
  ext i j
  by_cases hj : j = 0
  · subst j
    induction i using Fin.lastCases with
    | last =>
      have hm : (0 : Fin (n + 1)) ∉ (shiftedLowerSliceColumns n (Fin.last n))ᶜ := by
        simp [shiftedLowerSliceColumns]
      change (if h : (0 : Fin (n + 1)) ∈ (shiftedLowerSliceColumns n (Fin.last n))ᶜ then _
        else trailingIdentity n (Fin.last n) 0) = _
      rw [dite_eq_right hm, mul_firstColumn_last_zero]
      simp [trailingIdentity]
    | cast i =>
      rw [upperFreeParam_firstColumn, mul_firstColumn_castSucc]
  · rw [mul_firstColumn_of_ne_zero u v i j hj]
    by_cases hij : i < j
    · exact (upperFreeParam_upperEntry n _ ⟨(i, j), hij⟩).trans
        (upperEntryCoordinates_apply u ⟨(i, j), hij⟩)
    · have hm : j ∉ (shiftedLowerSliceColumns n i)ᶜ := by
        apply Finset.notMem_compl.mpr
        simp only [shiftedLowerSliceColumns, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨Fin.pos_of_ne_zero hj, le_of_not_gt hij⟩
      change (if h : j ∈ (shiftedLowerSliceColumns n i)ᶜ then _ else trailingIdentity n i j) = _
      rw [dite_eq_right hm]
      by_cases he : i = j
      · subst j
        simp [trailingIdentity, hj, UpperUnipotent.entry_diag]
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm he)
        rw [UpperUnipotent.entry_eq_zero u hji]
        simp [trailingIdentity, he]

/-- Actual upper-unipotent multiplication realizes the upper slice with exactly
the supplied strict-upper scalar product and first-column row measure. -/
theorem upper_unipotent_product_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving
      (fun z : (UpperEntryPair (n + 1) → K) × (Fin n → K) =>
        ((upperEntryCoordinates (n + 1)).symm z.1).val.val * firstColumnMatrix n z.2)
      ((upperEntryProductMeasure ν (n + 1)).prod (rowMeasure ν n))
      (upperFirstColumnSliceMeasure ν n) := by
  have he : (fun z : (UpperEntryPair (n + 1) → K) × (Fin n → K) =>
      upperFreeParam n (z.1, upperColumnAction z.1 z.2)) =
      (fun z : (UpperEntryPair (n + 1) → K) × (Fin n → K) =>
        ((upperEntryCoordinates (n + 1)).symm z.1).val.val * firstColumnMatrix n z.2) := by
    funext z
    simpa only [Homeomorph.apply_symm_apply] using
      upperColumnParam_eq_mul n ((upperEntryCoordinates (n + 1)).symm z.1) z.2
  exact he ▸ upperColumnParam_preserving ν n

end Langlands.HarmonicAnalysis
