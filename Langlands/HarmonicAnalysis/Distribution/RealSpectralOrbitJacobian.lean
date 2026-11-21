import Langlands.HarmonicAnalysis.Distribution.RealSpectralActionCovariance
import Langlands.HarmonicAnalysis.Distribution.WeightedChartTransition
import Langlands.HarmonicAnalysis.Distribution.ZeroNormalOrbitChart
import Langlands.LinearAlgebra.RealSpectralChartDerivative

/-! # The orbit Jacobian at a fixed real spectral slice point -/

noncomputable section

open Filter Function
open scoped ContDiff Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

private theorem chart_derivative_intertwines_fixed {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {e : OpenPartialHomeomorph E X} (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) (L : X ≃L[ℝ] X)
    {p : E} (hp : p ∈ e.source) (hfix : L (e p) = e p) :
    (fderiv ℝ e p).comp (fderiv ℝ (chartLinearTransition e L) p) =
      L.toContinuousLinearMap.comp (fderiv ℝ e p) := by
  let D := fderiv ℝ e p
  let I := fderiv ℝ e.symm (e p)
  have hD : HasFDerivAt e D p :=
    ((he.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hI : HasFDerivAt e.symm I (L (e p)) := by
    rw [hfix]
    exact ((hei.contDiffAt (e.open_target.mem_nhds (e.map_source hp))).differentiableAt
      (by simp)).hasFDerivAt
  have hH : HasFDerivAt (chartLinearTransition e L)
      (I.comp (L.toContinuousLinearMap.comp D)) p :=
    hI.comp p (L.toContinuousLinearMap.hasFDerivAt.comp p hD)
  rw [hH.fderiv]
  ext1 v
  exact (chartFDerivEquiv he hei hp).apply_symm_apply (L (D v))

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A

variable {A : Matrix (Fin n) (Fin n) ℝ} {W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
  {N : Submodule ℝ W}

local notation "Coord" => ((T[A] × Z[A]) × N)

/-- The orbit block of the chart derivative at a semisimple slice point,
viewed in the fixed tangent space when the shifted tangent agrees with it. -/
def realMatrixStratumChartOrbitMap (J : T[A] →L[ℝ] Mat) (z : Z[A])
    (hT : T[A + (z : Mat)] = T[A]) : T[A] →ₗ[ℝ] T[A] :=
  ((matrixConjugationTangent (A + (z : Mat))).comp J.toLinearMap).codRestrict T[A] (fun v => by
    let X := matrixConjugationTangent (A + (z : Mat)) (J v)
    have hm : X ∈ T[A + (z : Mat)] := LinearMap.mem_range_self _ _
    exact (congrArg (fun S : Submodule ℝ Mat => X ∈ S) hT).mp hm)

variable (J : T[A] →L[ℝ] Matrix (Fin n) (Fin n) ℝ)
  {e : OpenPartialHomeomorph ((T[A] × Z[A]) × N) (Matrix (Fin n) (Fin n) ℝ)}
  (hformula : ∀ p, e p = (1 + J p.1.1) * (A + ↑p.1.2 + ↑(p.2 : W)) *
    Ring.inverse (1 + J p.1.1))
  (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
  (z : Z[A]) (hz : ((0, z), 0) ∈ e.source)
  (hT : T[A + (z : Matrix (Fin n) (Fin n) ℝ)] = T[A])

set_option maxHeartbeats 700000 in
include hformula he hei hz hT in
/-- At a fixed slice point the orbit block of the coordinate transition is
conjugate to the ambient action on the orbit tangent. -/
theorem det_zeroNormalOrbitDerivative_chartLinearTransition (L : Mat ≃L[ℝ] Mat)
    (hfix : L (A + (z : Mat)) = A + (z : Mat))
    (hLT : T[A] ≤ T[A].comap L.toLinearEquiv.toLinearMap) :
    LinearMap.det
        (zeroNormalOrbitDerivative (N := N) (chartLinearTransition e L) ((0 : T[A]), z)).toLinearMap =
      LinearMap.det (L.toLinearEquiv.toLinearMap.restrict (p := T[A]) (q := T[A]) hLT) := by
  let p : Coord := ((0, z), 0)
  let D := realMatrixStratumChartDerivative (N := N) J z
  let Ψ : OpenPartialHomeomorph Coord Coord := chartLinearTransition (E := Coord) e L
  let H := fderiv ℝ Ψ p
  have he_p : e p = A + (z : Mat) := by rw [hformula]; simp [p]
  have hL_p : L (e p) = e p := by rw [he_p, hfix]
  have hD : HasFDerivAt e D p := hasFDerivAt_realMatrixStratumChart_slice J e hformula z
  have hDH : D.comp H = L.toContinuousLinearMap.comp D := by
    rw [← hD.fderiv]
    exact chart_derivative_intertwines_fixed (e := e) he hei L (p := p) hz hL_p
  have hDin : Injective D := by
    rw [← hD.fderiv]
    exact (chartFDerivEquiv he hei hz).injective
  let P := realMatrixStratumChartOrbitMap J z hT
  have hP (v : T[A]) : (P v : Mat) = D ((v, 0), 0) := by
    simp [P, D, realMatrixStratumChartOrbitMap]
  have hPin : Injective P := by
    intro v w hvw
    have h := congrArg (fun t : T[A] => (t : Mat)) hvw
    rw [hP, hP] at h
    exact congrArg (fun c : Coord => c.1.1) (hDin h)
  let Q := LinearEquiv.ofInjectiveEndo P hPin
  let R := L.toLinearEquiv.toLinearMap.restrict (p := T[A]) (q := T[A]) hLT
  have hconj : (zeroNormalOrbitDerivative (N := N) Ψ ((0 : T[A]), z)).toLinearMap =
      Q.symm.conj R := by
    ext1 v
    let w := Q.symm (R (Q v))
    have hPw : P w = R (P v) := Q.apply_symm_apply (R (Q v))
    have hDw : D ((w, 0), 0) = L (D ((v, 0), 0)) := by
      have h := congrArg (fun t : T[A] => (t : Mat)) hPw
      change (P w : Mat) = L (P v : Mat) at h
      simpa only [hP] using h
    have hDv : D (H ((v, 0), 0)) = L (D ((v, 0), 0)) :=
      DFunLike.congr_fun hDH ((v, 0), 0)
    have hv : H ((v, 0), 0) = ((w, 0), 0) := hDin (hDv.trans hDw.symm)
    change (H ((v, 0), 0)).1.1 = w
    exact congrArg (fun c : Coord => c.1.1) hv
  change LinearMap.det (zeroNormalOrbitDerivative (N := N) Ψ ((0 : T[A]), z)).toLinearMap =
    LinearMap.det R
  rw [hconj]
  exact LinearMap.det_conj R Q.symm

include hformula he hei hz hT in
theorem zeroNormalOrbitJacobian_realSpectralConjugation {u : Matˣ}
    (hu : Commute (u : Mat) A) :
    zeroNormalOrbitJacobian (N := N) (chartLinearTransition e (fullConjugationEquiv u))
      ((0 : T[A]), z) = 1 := by
  have hLT := fullConjugationEquiv_preserves_tangent hu
  have hfix : fullConjugationEquiv u (A + (z : Mat)) = A + (z : Mat) :=
    conjugate_add_semisimpleDirection_eq hu z.property
  change |LinearMap.det (zeroNormalOrbitDerivative (N := N)
    (chartLinearTransition e (fullConjugationEquiv u)) ((0 : T[A]), z)).toLinearMap| = 1
  rw [det_zeroNormalOrbitDerivative_chartLinearTransition J hformula he hei z hz hT _ hfix hLT]
  exact abs_det_matrixConjugationOrbitTangent hu hLT

include hformula he hei hz hT in
theorem zeroNormalOrbitJacobian_realSpectralAdjustedTranspose {q : Matˣ}
    (hq : q.val * A * q.inv = Aᵀ) :
    zeroNormalOrbitJacobian (N := N) (chartLinearTransition e (fullAdjustedTransposeEquiv q))
      ((0 : T[A]), z) = 1 := by
  have hLT := fullAdjustedTransposeEquiv_preserves_tangent hq
  have hfix : fullAdjustedTransposeEquiv q (A + (z : Mat)) = A + (z : Mat) :=
    adjustedTranspose_add_semisimpleDirection_eq hq z.property
  change |LinearMap.det (zeroNormalOrbitDerivative (N := N)
    (chartLinearTransition e (fullAdjustedTransposeEquiv q)) ((0 : T[A]), z)).toLinearMap| = 1
  rw [det_zeroNormalOrbitDerivative_chartLinearTransition J hformula he hei z hz hT _ hfix hLT]
  exact abs_det_matrixAdjustedTransposeOrbitTangent hq hLT

end Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
