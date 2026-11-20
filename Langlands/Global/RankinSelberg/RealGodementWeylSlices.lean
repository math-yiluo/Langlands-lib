import Langlands.Global.RankinSelberg.RealGodementRectangularFourier
import Langlands.Representation.RankinSelberg.UnequalRankBlockCoordinates

/-! # The two Weyl slices in the real Godement Fourier identity -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "I" => Fin m × Fin (m + 1)
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ

/-- Free entries of a column followed by a lower unitriangular block. -/
abbrev StepCoordinates (m : ℕ) := {q : Fin m × Fin (m + 1) // q.2.val ≤ q.1.val}

/-- The rectangular lower-unipotent chart `[x,v]` for an upper triangular
inducing Borel. The first column is free, including in the first row. -/
def stepRectangle (z : StepCoordinates m → ℝ) : X := fun i j =>
  if h : j.val ≤ i.val then z ⟨(i, j), h⟩ else if j.val = i.val + 1 then 1 else 0

private def stepEdge (q : StepCoordinates m) : ℝ :=
  if q.val.2.val = q.val.1.val then 1 else 0

/-- The simple lower-unipotent coordinates in the rectangular chart. -/
def stepPhase (z : StepCoordinates m → ℝ) : ℝ := ∑ q, z q * stepEdge q

private abbrev firstSet (m : ℕ) (q : Fin m × Fin (m + 1)) : Prop := m ≤ q.1.val + q.2.val

local notation "A" => {q : I // firstSet m q}
local notation "B" => {q : I // ¬firstSet m q}

private def columnReversal : StepCoordinates m ≃ A where
  toFun q := ⟨(q.val.1, q.val.2.rev), by
    have h := q.property
    have hj := q.val.2.isLt
    simp only [firstSet, Fin.val_rev]
    omega⟩
  invFun q := ⟨(q.val.1, q.val.2.rev), by
    have h := q.property
    have hj := q.val.2.isLt
    simp only [firstSet] at h
    simp only [Fin.val_rev]
    omega⟩
  left_inv q := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)

private def rowReversal : StepCoordinates m ≃ B where
  toFun q := ⟨(q.val.1.rev, q.val.2), by
    have h := q.property
    have hi := q.val.1.isLt
    simp only [firstSet, Fin.val_rev]
    omega⟩
  invFun q := ⟨(q.val.1.rev, q.val.2), by
    have h := q.property
    have hi := q.val.1.isLt
    simp only [firstSet] at h
    simp only [Fin.val_rev]
    omega⟩
  left_inv q := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)

private def firstEdge (q : A) : ℝ := if q.val.1.val + q.val.2.val = m then 1 else 0
private def secondEdge (q : B) : ℝ := if q.val.1.val + q.val.2.val + 1 = m then 1 else 0

private theorem firstEdge_columnReversal (q : StepCoordinates m) :
    firstEdge (columnReversal q) = stepEdge q := by
  have hj := q.val.2.isLt
  have h : q.val.1.val + q.val.2.rev.val = m ↔ q.val.2.val = q.val.1.val := by
    rw [Fin.val_rev]
    omega
  change (if q.val.1.val + q.val.2.rev.val = m then (1 : ℝ) else 0) = stepEdge q
  simp only [h, stepEdge]

private theorem secondEdge_rowReversal (q : StepCoordinates m) :
    secondEdge (rowReversal q) = stepEdge q := by
  have hi := q.val.1.isLt
  have h : q.val.1.rev.val + q.val.2.val + 1 = m ↔ q.val.2.val = q.val.1.val := by
    rw [Fin.val_rev]
    omega
  change (if q.val.1.rev.val + q.val.2.val + 1 = m then (1 : ℝ) else 0) = stepEdge q
  simp only [h, stepEdge]

private theorem reindex_phase {J : Type} [Fintype J] (e : StepCoordinates m ≃ J)
    (b : J → ℝ) (hb : ∀ q, b (e q) = stepEdge q) (z : StepCoordinates m → ℝ) :
    (∑ j, MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e z j * b j) = stepPhase z := by
  symm
  unfold stepPhase
  refine Fintype.sum_equiv e _ _ (fun q => ?_)
  rw [MeasurableEquiv.piCongrLeft_apply_apply, hb]

private theorem stepRectangle_mul_weylLong (z : StepCoordinates m → ℝ) (i : Fin m) (j : Fin (m + 1)) :
    (stepRectangle z * (weylLong (m + 1) ℝ).val) i j = stepRectangle z i j.rev := by
  simp only [Matrix.mul_apply, weylLong_entry, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem join_columnReversal (z : StepCoordinates m → ℝ) :
    joinRectangularCoordinates (firstSet m)
      (MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) columnReversal z) secondEdge =
      stepRectangle z * (weylLong (m + 1) ℝ).val := by
  ext i j
  rw [stepRectangle_mul_weylLong]
  have hj := j.isLt
  have hFree : j.rev.val ≤ i.val ↔ firstSet m (i, j) := by
    simp only [firstSet, Fin.val_rev]
    omega
  have hEdge : j.rev.val = i.val + 1 ↔ i.val + j.val + 1 = m := by
    rw [Fin.val_rev]
    omega
  by_cases h : firstSet m (i, j)
  · have hz := hFree.mpr h
    simp only [joinRectangularCoordinates, dite_eq_left h, stepRectangle, dite_eq_left hz]
    have hIndex : columnReversal ⟨(i, j.rev), hz⟩ = (⟨(i, j), h⟩ : A) :=
      Subtype.ext (by simp [columnReversal])
    rw [← hIndex, MeasurableEquiv.piCongrLeft_apply_apply]
  · simp only [joinRectangularCoordinates, dite_eq_right h, stepRectangle, dite_eq_right (hFree.not.mpr h),
      secondEdge, hEdge]

private theorem join_rowReversal (z : StepCoordinates m → ℝ) :
    joinRectangularCoordinates (firstSet m) firstEdge
      (MeasurableEquiv.piCongrLeft (fun _ : B => ℝ) rowReversal z) =
      (weylLong m ℝ).val * stepRectangle z := by
  ext i j
  rw [Langlands.RankinSelberg.weylLong_mul_apply]
  have hi := i.isLt
  have hFree : j.val ≤ i.rev.val ↔ ¬firstSet m (i, j) := by
    simp only [firstSet, Fin.val_rev]
    omega
  have hEdge : j.val = i.rev.val + 1 ↔ i.val + j.val = m := by
    rw [Fin.val_rev]
    omega
  by_cases h : firstSet m (i, j)
  · have hz : ¬j.val ≤ i.rev.val := fun hn => hFree.mp hn h
    simp only [joinRectangularCoordinates, dite_eq_left h, stepRectangle, dite_eq_right hz, firstEdge, hEdge]
  · have hz := hFree.mpr h
    simp only [joinRectangularCoordinates, dite_eq_right h, stepRectangle, dite_eq_left hz]
    have hIndex : rowReversal ⟨(i.rev, j), hz⟩ = (⟨(i, j), h⟩ : B) :=
      Subtype.ext (by simp [rowReversal])
    rw [← hIndex, MeasurableEquiv.piCongrLeft_apply_apply]

/-- Fourier inversion on the two complementary Weyl slices in Jacquet's
Godement calculation, adapted to the upper Borel and the positive transform. -/
def RealGodementWeylSlicesStatement : Prop :=
  ∀ (m : ℕ) (a : ℝˣ) (Φ : 𝓢(Matrix (Fin m) (Fin (m + 1)) ℝ, ℂ)),
    let μ := Measure.pi fun _ : StepCoordinates m => (realSelfDualMeasure a).measure
    let f := fun z : StepCoordinates m → ℝ =>
      Φ (stepRectangle z * (weylLong (m + 1) ℝ).val) * (realScaledCharacter a).complex (stepPhase z)
    let g := fun z : StepCoordinates m → ℝ => realRectangularSchwartzFourier a Φ
      ((weylLong m ℝ).val * stepRectangle z) * (realScaledCharacter a).complex (-stepPhase z)
    Integrable f μ ∧ Integrable g μ ∧ (∫ z, g z ∂μ) = ∫ z, f z ∂μ

private theorem godementWeylSlices (a : ℝˣ) (Φ : 𝓢(X, ℂ)) :
    let μ := Measure.pi fun _ : StepCoordinates m => (realSelfDualMeasure a).measure
    let f := fun z : StepCoordinates m → ℝ =>
      Φ (stepRectangle z * (weylLong (m + 1) ℝ).val) * (realScaledCharacter a).complex (stepPhase z)
    let g := fun z : StepCoordinates m → ℝ => realRectangularSchwartzFourier a Φ
      ((weylLong m ℝ).val * stepRectangle z) * (realScaledCharacter a).complex (-stepPhase z)
    Integrable f μ ∧ Integrable g μ ∧ (∫ z, g z ∂μ) = ∫ z, f z ∂μ := by
  dsimp only
  let μ := (realSelfDualMeasure a).measure
  let P := MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) columnReversal
  let Q := MeasurableEquiv.piCongrLeft (fun _ : B => ℝ) rowReversal
  have hP := measurePreserving_piCongrLeft (fun _ : A => μ) columnReversal
  have hQ := measurePreserving_piCongrLeft (fun _ : B => μ) rowReversal
  let f := fun x : A → ℝ => Φ (joinRectangularCoordinates (firstSet m) x secondEdge) *
    (realScaledCharacter a).complex (∑ i, x i * firstEdge i)
  let g := fun y : B → ℝ => realRectangularSchwartzFourier a Φ
    (joinRectangularCoordinates (firstSet m) firstEdge y) *
    (realScaledCharacter a).complex (-(∑ i, y i * secondEdge i))
  have ⟨hf, hg, heq⟩ : Integrable f (Measure.pi fun _ : A => μ) ∧
      Integrable g (Measure.pi fun _ : B => μ) ∧
      (∫ y, g y ∂Measure.pi (fun _ : B => μ)) = ∫ x, f x ∂Measure.pi (fun _ : A => μ) :=
    realGodementRectangularFourier m (m + 1) (firstSet m) a Φ firstEdge secondEdge
  have hf' (z : StepCoordinates m → ℝ) : f (P z) =
      Φ (stepRectangle z * (weylLong (m + 1) ℝ).val) * (realScaledCharacter a).complex (stepPhase z) := by
    dsimp only [f, P]
    rw [join_columnReversal, reindex_phase columnReversal firstEdge firstEdge_columnReversal]
  have hg' (z : StepCoordinates m → ℝ) : g (Q z) = realRectangularSchwartzFourier a Φ
      ((weylLong m ℝ).val * stepRectangle z) * (realScaledCharacter a).complex (-stepPhase z) := by
    dsimp only [g, Q]
    rw [join_rowReversal, reindex_phase rowReversal secondEdge secondEdge_rowReversal]
  refine ⟨(hP.integrable_comp_of_integrable hf).congr (Filter.Eventually.of_forall hf'),
    (hQ.integrable_comp_of_integrable hg).congr (Filter.Eventually.of_forall hg'), ?_⟩
  calc
    _ = ∫ z, g (Q z) ∂Measure.pi (fun _ : StepCoordinates m => μ) :=
      (integral_congr_ae (Filter.Eventually.of_forall hg')).symm
    _ = ∫ y, g y ∂Measure.pi (fun _ : B => μ) := hQ.integral_comp' g
    _ = ∫ x, f x ∂Measure.pi (fun _ : A => μ) := heq
    _ = ∫ z, f (P z) ∂Measure.pi (fun _ : StepCoordinates m => μ) := (hP.integral_comp' f).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hf')

theorem realGodementWeylSlices : RealGodementWeylSlicesStatement := by
  intro m a Φ
  exact godementWeylSlices a Φ

end Langlands.Global.RankinSelbergGlobal.RealGodement
