import Langlands.LinearAlgebra.MatrixOrbitTangentDeterminant
import Langlands.LinearAlgebra.RealSpectralStratumChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Local actions on the real spectral stratum chart -/

noncomputable section

open Matrix Filter
open scoped ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A

/-- Transport an ambient linear equivalence to the overlap of a chart with its inverse image. -/
def realMatrixChartAction {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph E Mat) (L : Mat ≃L[ℝ] Mat) : OpenPartialHomeomorph E E :=
  (e.transHomeomorph L.toHomeomorph).trans e.symm

@[simp]
theorem realMatrixChartAction_apply {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph E Mat) (L : Mat ≃L[ℝ] Mat) (p : E) :
    realMatrixChartAction e L p = e.symm (L (e p)) := rfl

@[simp]
theorem mem_realMatrixChartAction_source {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph E Mat) (L : Mat ≃L[ℝ] Mat) (p : E) :
    p ∈ (realMatrixChartAction e L).source ↔ p ∈ e.source ∧ L (e p) ∈ e.target := by
  rw [realMatrixChartAction, OpenPartialHomeomorph.trans_source]
  rfl

@[simp]
theorem realMatrixChartAction_symm_apply {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph E Mat) (L : Mat ≃L[ℝ] Mat) (p : E) :
    (realMatrixChartAction e L).symm p = e.symm (L.symm (e p)) := rfl

@[simp]
theorem mem_realMatrixChartAction_target {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph E Mat) (L : Mat ≃L[ℝ] Mat) (p : E) :
    p ∈ (realMatrixChartAction e L).target ↔ p ∈ e.source ∧ L.symm (e p) ∈ e.target := by
  rw [realMatrixChartAction, OpenPartialHomeomorph.trans_target]
  rfl

theorem contDiffOn_realMatrixChartAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E Mat) (L : Mat ≃L[ℝ] Mat)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (realMatrixChartAction e L) (realMatrixChartAction e L).source := by
  let U := (realMatrixChartAction e L).source
  have hf : ContDiffOn ℝ ∞ (fun p => L (e p)) U :=
    L.contDiff.contDiffOn.comp (he.mono fun p hp => ((mem_realMatrixChartAction_source e L p).mp hp).1)
      (fun _ _ => Set.mem_univ _)
  have hm : Set.MapsTo (fun p => L (e p)) U e.target :=
    fun p hp => ((mem_realMatrixChartAction_source e L p).mp hp).2
  exact hi.comp hf hm

theorem contDiffOn_realMatrixChartAction_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E Mat) (L : Mat ≃L[ℝ] Mat)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (realMatrixChartAction e L).symm (realMatrixChartAction e L).target := by
  have h : (realMatrixChartAction e L).target = (realMatrixChartAction e L.symm).source := by
    ext p
    simp
  rw [h]
  exact contDiffOn_realMatrixChartAction e L.symm he hi

private def transposeMatrixUnit (u : Matˣ) : Matˣ where
  val := u.valᵀ
  inv := u.invᵀ
  val_inv := by rw [← transpose_mul, u.inv_val, transpose_one]
  inv_val := by rw [← transpose_mul, u.val_inv, transpose_one]

theorem exists_intertwiner_matrixConjugationLinearEquiv (b u : Matˣ) (B : Mat) :
    ∃ v : Matˣ, v.val * matrixConjugationLinearEquiv b B =
      matrixConjugationLinearEquiv b (u.val * B * u.inv) * v.val := by
  refine ⟨b * u * b⁻¹, ?_⟩
  simp [mul_assoc]

theorem exists_intertwiner_matrixAdjustedTransposeLinearEquiv (q u : Matˣ) (B : Mat) :
    ∃ v : Matˣ, v.val * matrixAdjustedTransposeLinearEquiv q B =
      matrixAdjustedTransposeLinearEquiv q (u.val * B * u.inv) * v.val := by
  let w := transposeMatrixUnit u
  obtain ⟨v, hv⟩ := exists_intertwiner_matrixConjugationLinearEquiv q⁻¹ w⁻¹ Bᵀ
  refine ⟨v, ?_⟩
  change v.val * (q.inv * Bᵀ * q.val) =
    q.inv * (u.invᵀ * Bᵀ * u.valᵀ) * q.val * v.val at hv
  simpa only [matrixAdjustedTransposeLinearEquiv_apply, transpose_mul, mul_assoc] using hv

section Slice

variable {A : Matrix (Fin n) (Fin n) ℝ} {W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
  {N : Submodule ℝ W}

local notation:max "Coord" => ((T[A] × Z[A]) × N)

/-- At a slice point fixed by the ambient action, the local chart action fixes the coordinates. -/
theorem realMatrixChartAction_slice_fixed
    (J : T[A] →L[ℝ] Mat) (e : OpenPartialHomeomorph Coord Mat)
    (he : ∀ p, e p = (1 + J p.1.1) * (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) *
      Ring.inverse (1 + J p.1.1))
    (L : Mat ≃L[ℝ] Mat) (z : Z[A]) (hz : ((0, z), 0) ∈ e.source)
    (hL : L (A + (z : Mat)) = A + (z : Mat)) :
    ((0, z), 0) ∈ (realMatrixChartAction e L).source ∧
      realMatrixChartAction e L ((0, z), 0) = ((0, z), 0) := by
  have hez : e ((0, z), 0) = A + (z : Mat) := by rw [he]; simp
  have hpoint : L (e ((0, z), 0)) = e ((0, z), 0) := by rw [hez, hL]
  exact ⟨(mem_realMatrixChartAction_source e L _).mpr ⟨hz, hpoint.symm ▸ e.map_source hz⟩,
    by rw [realMatrixChartAction_apply, hpoint, e.left_inv hz]⟩

/-- The nearby zero-normal plane is preserved with its semisimple coordinate when the ambient
linear action fixes the slice and carries similar matrices to similar matrices. -/
theorem eventually_realMatrixChartAction_preserves_plane
    (J : T[A] →L[ℝ] Mat) (e : OpenPartialHomeomorph Coord Mat) (V : Set (Mat × Mat))
    (he : ∀ p, e p = (1 + J p.1.1) * (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) *
      Ring.inverse (1 + J p.1.1)) (heunit : ∀ p ∈ e.source, IsUnit (1 + J p.1.1))
    (hV : IsOpen V)
    (hrec : ∀ (w : Z[A]) (B : Mat), (A + (w : Mat), B) ∈ V →
      (∃ u : Matˣ, u.val * (A + (w : Mat)) = B * u.val) →
      B ∈ e.target ∧ (e.symm B).1.2 = w ∧ (e.symm B).2 = 0)
    (L : Mat ≃L[ℝ] Mat)
    (hLsim : ∀ (u : Matˣ) (B : Mat), ∃ v : Matˣ, v.val * L B = L (u.val * B * u.inv) * v.val)
    (hL : ∀ w : Z[A], L (A + (w : Mat)) = A + (w : Mat))
    (z : Z[A]) (hz : ((0, z), 0) ∈ e.source) (hzV : (A + (z : Mat), A + (z : Mat)) ∈ V) :
    ∀ᶠ p : T[A] × Z[A] in 𝓝 (0, z),
      (p, 0) ∈ (realMatrixChartAction e L).source ∧
        (realMatrixChartAction e L (p, 0)).1.2 = p.2 ∧
        (realMatrixChartAction e L (p, 0)).2 = 0 := by
  let f : (T[A] × Z[A]) → Coord := fun p => (p, 0)
  have hf : Continuous f := continuous_id.prodMk continuous_const
  have hs : ∀ᶠ p in 𝓝 ((0 : T[A]), z), f p ∈ e.source :=
    hf.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hz)
  have hchart : ContinuousAt (e : Coord → Mat) (f (0, z)) :=
    e.continuousOn.continuousAt (e.open_source.mem_nhds hz)
  have hEf : ContinuousAt (fun p : T[A] × Z[A] => e (f p)) (0, z) := hchart.comp hf.continuousAt
  have hcont : ContinuousAt (fun p : T[A] × Z[A] => (A + (p.2 : Mat), L (e (f p)))) (0, z) :=
    (continuous_const.add (continuous_subtype_val.comp continuous_snd)).continuousAt.prodMk
      (L.continuous.continuousAt.comp hEf)
  have hez : e (f (0, z)) = A + (z : Mat) := by rw [he]; simp [f]
  have hV' : ∀ᶠ p : T[A] × Z[A] in 𝓝 (0, z), (A + (p.2 : Mat), L (e (f p))) ∈ V :=
    hcont.preimage_mem_nhds (hV.mem_nhds (by rw [hez, hL]; exact hzV))
  filter_upwards [hs, hV'] with p hp hVp
  obtain ⟨u, hu⟩ := heunit (f p) hp
  have hep : e (f p) = u.val * (A + (p.2 : Mat)) * u.inv := by
    rw [he]
    change (1 + J p.1) * (A + (p.2 : Mat) + 0) * Ring.inverse (1 + J p.1) = _
    change u.val = 1 + J p.1 at hu
    rw [add_zero, ← hu, Ring.inverse_unit]
    rfl
  obtain ⟨v, hv⟩ := hLsim u (A + (p.2 : Mat))
  rw [hL, ← hep] at hv
  obtain ⟨hTarget, hZ, hNormal⟩ := hrec p.2 (L (e (f p))) hVp ⟨v, hv⟩
  exact ⟨(mem_realMatrixChartAction_source e L _).mpr ⟨hp, hTarget⟩, hZ, hNormal⟩

end Slice

end Langlands
