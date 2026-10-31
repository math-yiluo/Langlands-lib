import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAffineSlice

/-! Actual free-coordinate parametrizations of affine matrix slice measures. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uI uJ uK

/-- Grouping a finite family of independent coordinates into rows preserves the
actual product measure. No Haar or normalization hypothesis is used. -/
theorem finitePiCurry_preserving {ι : Type uI} {κ : ι → Type uJ}
    [Fintype ι] [∀ i, Fintype (κ i)] {X : (i : ι) → κ i → Type uK}
    [∀ i j, MeasurableSpace (X i j)]
    (μ : (i : ι) → (j : κ i) → Measure (X i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi (fun p : Sigma κ => μ p.1 p.2))
      (Measure.pi (fun i => Measure.pi (μ i))) := by
  classical
  refine ⟨(MeasurableEquiv.piCurry X).measurable, ?_⟩
  symm
  apply Measure.pi_eq_generateFrom
    (C := fun i => Set.pi Set.univ '' Set.pi Set.univ
      (fun j => {s : Set (X i j) | MeasurableSet s}))
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi (fun j => (μ i j).toFiniteSpanningSetsIn))
  intro s hs
  choose t ht hts using hs
  rw [← funext hts]
  have hm : MeasurableSet (Set.univ.pi fun i => Set.univ.pi (t i)) :=
    MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => ht i j (Set.mem_univ j)
  rw [Measure.map_apply (MeasurableEquiv.piCurry X).measurable hm]
  have he : (MeasurableEquiv.piCurry X) ⁻¹' (Set.univ.pi fun i => Set.univ.pi (t i)) =
      Set.univ.pi (fun p : Sigma κ => t p.1 p.2) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    change (∀ i j, x ⟨i, j⟩ ∈ t i j) ↔ ∀ p : Sigma κ, x p ∈ t p.1 p.2
    exact ⟨fun h p => h p.1 p.2, fun h i j => h ⟨i, j⟩⟩
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Fintype.prod_sigma _

variable {K : Type uK} [Field K] [TopologicalSpace K] [MeasurableSpace K]

/-- Fill the selected row coordinates with free values, and fix the others at c. -/
def coordinateSliceParam {d : ℕ} (S : Finset (Fin d)) (c : Fin d → K)
    (x : {i : Fin d // i ∈ S} → K) : Fin d → K :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else c i

private instance sliceEntry_sigmaFinite (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {d : ℕ} (S : Finset (Fin d)) (c : Fin d → K) (i : Fin d) :
    SigmaFinite (if i ∈ S then ν.measure else Measure.dirac (c i)) := by
  split_ifs <;> infer_instance

private instance sliceRow_sigmaFinite (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {d : ℕ} (S : Finset (Fin d)) (c : Fin d → K) :
    SigmaFinite (coordinateSliceMeasure ν S c) := by
  unfold coordinateSliceMeasure
  infer_instance

/-- Parametrizing the free coordinates pushes their actual scalar product
measure to the published coordinate slice measure. -/
theorem coordinateSliceParam_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {d : ℕ} (S : Finset (Fin d)) (c : Fin d → K) :
    MeasurePreserving (coordinateSliceParam S c)
      (Measure.pi (fun _ : {i : Fin d // i ∈ S} => ν.measure))
      (coordinateSliceMeasure ν S c) := by
  classical
  have hm : Measurable (coordinateSliceParam S c) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i ∈ S
    · simpa only [coordinateSliceParam, dite_eq_left hi] using
        (measurable_pi_apply (⟨i, hi⟩ : {i : Fin d // i ∈ S}))
    · simpa only [coordinateSliceParam, dite_eq_right hi] using (measurable_const (a := c i))
  refine ⟨hm, ?_⟩
  symm
  unfold coordinateSliceMeasure
  apply Measure.pi_eq
  intro t ht
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun i => ht i)]
  by_cases hc : ∀ i, i ∉ S → c i ∈ t i
  · have he : coordinateSliceParam S c ⁻¹' Set.univ.pi t =
        Set.univ.pi (fun i : {i : Fin d // i ∈ S} => t i) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · intro hx i
        simpa only [coordinateSliceParam, dite_eq_left i.2] using hx i
      · intro hx i
        by_cases hi : i ∈ S
        · simpa only [coordinateSliceParam, dite_eq_left hi] using hx ⟨i, hi⟩
        · simpa only [coordinateSliceParam, dite_eq_right hi] using hc i hi
    rw [he, Measure.pi_pi]
    have hf (i : Fin d) :
        (if i ∈ S then ν.measure else Measure.dirac (c i)) (t i) =
          if i ∈ S then ν.measure (t i) else 1 := by
      split_ifs with hi
      · rfl
      · exact Measure.dirac_apply_of_mem (hc i hi)
    simp_rw [hf]
    have hp (i : {i : Fin d // i ∈ S}) :
        (if i.val ∈ S then ν.measure (t i.val) else 1) = ν.measure (t i.val) :=
      ite_eq_left i.2
    have hn (i : {i : Fin d // i ∉ S}) :
        (if i.val ∈ S then ν.measure (t i.val) else 1) = 1 := ite_eq_right i.2
    have hprod := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin d => i ∈ S)
      (fun i => if i ∈ S then ν.measure (t i) else 1)
    simp only [hp, hn, Finset.prod_const_one, mul_one] at hprod
    convert hprod using 1
    apply Finset.prod_congr
    · ext i
      simp
    · intro i _
      rfl
  · push Not at hc
    obtain ⟨i, hi, hci⟩ := hc
    have he : coordinateSliceParam S c ⁻¹' Set.univ.pi t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx' := (Set.mem_univ_pi.mp hx) i
      exact hci (by simpa only [coordinateSliceParam, dite_eq_right hi] using hx')
    rw [he, measure_empty]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right hi, Measure.dirac_apply' _ (ht i), Set.indicator_of_notMem hci]

/-- Free entries indexed by their row and their selected column within that row. -/
abbrev RectangularFreeEntry {r s : ℕ} (S : Fin r → Finset (Fin s)) :=
  (i : Fin r) × {j : Fin s // j ∈ S i}

/-- Parametrize an affine rectangular slice by its scalar free entries. -/
def rectangularSliceParam {r s : ℕ} (S : Fin r → Finset (Fin s))
    (c : Matrix (Fin r) (Fin s) K) (x : RectangularFreeEntry S → K) :
    Matrix (Fin r) (Fin s) K :=
  fun i => coordinateSliceParam (S i) (c i) (fun j => x ⟨i, j⟩)

/-- The actual free-entry product measure pushes forward to the actual nested
matrix slice measure, with no extra constant even for empty dimensions. -/
theorem rectangularSliceParam_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] {r s : ℕ} (S : Fin r → Finset (Fin s))
    (c : Matrix (Fin r) (Fin s) K) :
    MeasurePreserving (rectangularSliceParam S c)
      (Measure.pi (fun _ : RectangularFreeEntry S => ν.measure))
      (rectangularCoordinateSliceMeasure ν S c) := by
  let : ∀ i : Fin r, SigmaFinite (coordinateSliceMeasure ν (S i) (c i)) :=
    fun i => sliceRow_sigmaFinite ν (S i) (c i)
  have hrow := measurePreserving_pi
    (fun i : Fin r => Measure.pi (fun _ : {j : Fin s // j ∈ S i} => ν.measure))
    (fun i => coordinateSliceMeasure ν (S i) (c i))
    (fun i => coordinateSliceParam_preserving ν (S i) (c i))
  exact hrow.comp (finitePiCurry_preserving
    (X := fun i (_ : {j : Fin s // j ∈ S i}) => K) (fun _ _ => ν.measure))

end Langlands.HarmonicAnalysis
