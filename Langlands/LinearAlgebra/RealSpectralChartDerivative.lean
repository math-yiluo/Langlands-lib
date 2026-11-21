import Langlands.LinearAlgebra.RealSpectralNormalAction

/-! # Derivatives on the semisimple slice of the real spectral stratum chart -/

noncomputable section

open Matrix Filter
open scoped Matrix.Norms.Operator ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A

private theorem hasFDerivAt_affineMatrixConj_of_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (X Y : E →L[ℝ] Mat) (A : Mat) (p : E)
    (hX₀ : X p = 0) :
    HasFDerivAt (fun v => (1 + X v) * (A + Y v) * Ring.inverse (1 + X v))
      ((matrixConjugationTangent (A + Y p)).toContinuousLinearMap.comp X + Y) p := by
  have hX : HasFDerivAt (fun v => 1 + X v) X p := X.hasFDerivAt.const_add 1
  have hY : HasFDerivAt (fun v => A + Y v) Y p := Y.hasFDerivAt.const_add A
  have hI : HasFDerivAt Ring.inverse (-(1 : Mat →L[ℝ] Mat)) (1 : Mat) := by
    have he : ContinuousLinearMap.mulLeftRight ℝ Mat (1 : Mat) (1 : Mat) =
        (1 : Mat →L[ℝ] Mat) := by
      ext1 w
      simp [ContinuousLinearMap.mulLeftRight_apply]
    simpa only [inv_one, Units.val_one, he] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : Matˣ))
  have hIp : HasFDerivAt Ring.inverse (-(1 : Mat →L[ℝ] Mat)) ((fun v => 1 + X v) p) := by
    simpa only [hX₀, add_zero] using hI
  have hR : HasFDerivAt (fun v => Ring.inverse (1 + X v)) (-X) p := by
    have he : (-(1 : Mat →L[ℝ] Mat)).comp X = -X := by ext1; rfl
    simpa only [he, Function.comp_def] using hIp.comp p hX
  refine ((hX.fun_mul' hY).fun_mul' hR).congr_fderiv ?_
  ext1 w
  simp only [hX₀, add_zero, one_mul, Ring.inverse_one, _root_.add_apply, _root_.neg_apply,
    _root_.smul_apply, smul_eq_mul, op_smul_eq_mul, one_smul, mul_one, mul_neg,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', matrixConjugationTangent_apply]
  abel

section Coordinates

variable {A : Matrix (Fin n) (Fin n) ℝ} {W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
  {N : Submodule ℝ W}

local notation:max "Coord" => ((T[A] × Z[A]) × N)

/-- The slice derivative takes the orbit coordinate to its commutator at the shifted point and
embeds the other two coordinates linearly. -/
def realMatrixStratumChartDerivative (J : T[A] →L[ℝ] Mat) (z : Z[A]) : Coord →L[ℝ] Mat :=
  let t := (ContinuousLinearMap.fst ℝ T[A] Z[A]).comp (ContinuousLinearMap.fst ℝ (T[A] × Z[A]) N)
  let s := (ContinuousLinearMap.snd ℝ T[A] Z[A]).comp (ContinuousLinearMap.fst ℝ (T[A] × Z[A]) N)
  let r := ContinuousLinearMap.snd ℝ (T[A] × Z[A]) N
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Mat) (F' := Mat)
    (matrixConjugationTangent (A + (z : Mat)))).comp (J.comp t) +
    ((Z[A].subtypeL.comp s) + (W.subtypeL.comp N.subtypeL).comp r)

@[simp]
theorem realMatrixStratumChartDerivative_apply (J : T[A] →L[ℝ] Mat) (z : Z[A]) (p : Coord) :
    realMatrixStratumChartDerivative (N := N) J z p =
      matrixConjugationTangent (A + (z : Mat)) (J p.1.1) +
        ((p.1.2 : Mat) + ((p.2 : W) : Mat)) := rfl

theorem hasFDerivAt_realMatrixStratumChart_slice
    (J : T[A] →L[ℝ] Mat) (e : Coord → Mat)
    (he : ∀ p, e p = (1 + J p.1.1) * (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) *
      Ring.inverse (1 + J p.1.1)) (z : Z[A]) :
    HasFDerivAt e (realMatrixStratumChartDerivative (N := N) J z) ((0, z), 0) := by
  let t := (ContinuousLinearMap.fst ℝ T[A] Z[A]).comp (ContinuousLinearMap.fst ℝ (T[A] × Z[A]) N)
  let s := (ContinuousLinearMap.snd ℝ T[A] Z[A]).comp (ContinuousLinearMap.fst ℝ (T[A] × Z[A]) N)
  let r := ContinuousLinearMap.snd ℝ (T[A] × Z[A]) N
  let X := J.comp t
  let Y : Coord →L[ℝ] Mat := (Z[A].subtypeL.comp s) + (W.subtypeL.comp N.subtypeL).comp r
  have hx (p : Coord) : X p = J p.1.1 := rfl
  have hy (p : Coord) : Y p = (p.1.2 : Mat) + ((p.2 : W) : Mat) := rfl
  have hx₀ : X ((0, z), 0) = 0 := by rw [hx, map_zero]
  have hy₀ : Y ((0, z), 0) = (z : Mat) := by rw [hy]; simp
  have he' : e = fun p => (1 + X p) * (A + Y p) * Ring.inverse (1 + X p) := by
    funext p
    rw [he, hx, hy, add_assoc]
  rw [he']
  refine (hasFDerivAt_affineMatrixConj_of_eq_zero X Y A _ hx₀).congr_fderiv ?_
  rw [hy₀]
  rfl

variable (hZW : Z[A] ≤ W) (hTW : IsCompl T[A] W) (hN : IsCompl (Z[A].comap W.subtype) N)

theorem normalProjection_comp_realMatrixStratumChartDerivative
    (J : T[A] →L[ℝ] Mat) (z : Z[A])
    (hT : T[A + (z : Mat)] = T[A]) :
    (realMatrixStratumNormalProjection hZW hTW hN).comp (realMatrixStratumChartDerivative J z) =
      ContinuousLinearMap.snd ℝ (T[A] × Z[A]) N := by
  apply ContinuousLinearMap.ext
  intro p
  let t : T[A] := ⟨matrixConjugationTangent (A + (z : Mat)) (J p.1.1),
    hT.le (LinearMap.mem_range_self _ _)⟩
  change realMatrixStratumNormalProjection hZW hTW hN
    (matrixConjugationTangent (A + (z : Mat)) (J p.1.1) + ((p.1.2 : Mat) + ((p.2 : W) : Mat))) = p.2
  rw [← add_assoc]
  exact realMatrixStratumNormalProjection_sum hZW hTW hN t p.1.2 p.2

/-- On a small semisimple slice, the normal derivative of the inverse chart is the fixed
projection along the orbit and semisimple directions. -/
theorem hasFDerivAt_realMatrixStratumChart_inverse_normal
    (J : T[A] →L[ℝ] Mat) (e : OpenPartialHomeomorph Coord Mat)
    (he : ∀ p, e p = (1 + J p.1.1) * (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) *
      Ring.inverse (1 + J p.1.1)) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (z : Z[A]) (hz : ((0, z), 0) ∈ e.source) (hT : T[A + (z : Mat)] = T[A]) :
    HasFDerivAt (fun B => (e.symm B).2) (realMatrixStratumNormalProjection hZW hTW hN)
      (A + (z : Mat)) := by
  let p : Coord := ((0, z), 0)
  let B : Mat := A + (z : Mat)
  have hBp : e p = B := by rw [he]; simp [p, B]
  have hB : B ∈ e.target := hBp ▸ e.map_source hz
  have hp : e.symm B = p := by rw [← hBp, e.left_inv hz]
  let D := realMatrixStratumChartDerivative (N := N) J z
  let K := fderiv ℝ e.symm B
  have hK : HasFDerivAt e.symm K B :=
    ((hi.contDiffAt (e.open_target.mem_nhds hB)).differentiableAt (by simp)).hasFDerivAt
  have hD : HasFDerivAt e D (e.symm B) := by
    rw [hp]
    exact hasFDerivAt_realMatrixStratumChart_slice J e he z
  have hinv : (fun X : Mat => X) =ᶠ[𝓝 B] e ∘ e.symm := by
    filter_upwards [e.open_target.mem_nhds hB] with X hX
    exact (e.right_inv hX).symm
  have hDK : D.comp K = ContinuousLinearMap.id ℝ Mat :=
    ((hD.comp B hK).congr_of_eventuallyEq hinv).unique (hasFDerivAt_id B)
  have hP := normalProjection_comp_realMatrixStratumChartDerivative hZW hTW hN J z hT
  have hNormal : (ContinuousLinearMap.snd ℝ (T[A] × Z[A]) N).comp K =
      realMatrixStratumNormalProjection hZW hTW hN := by
    rw [← hP, ContinuousLinearMap.comp_assoc, hDK, ContinuousLinearMap.comp_id]
  exact (hK.snd).congr_fderiv hNormal

/-- At a slice point fixed by an ambient linear map, the normal block of its local chart
expression is the compression of that map to the chosen normal complement. -/
theorem hasFDerivAt_realMatrixStratumChartAction_normal
    (J : T[A] →L[ℝ] Mat) (e : OpenPartialHomeomorph Coord Mat)
    (he : ∀ p, e p = (1 + J p.1.1) * (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) *
      Ring.inverse (1 + J p.1.1)) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (z : Z[A]) (hz : ((0, z), 0) ∈ e.source) (hT : T[A + (z : Mat)] = T[A])
    (L : Mat →L[ℝ] Mat) (hL : L (A + (z : Mat)) = A + (z : Mat)) :
    HasFDerivAt (fun y : N => (e.symm (L (e ((0, z), y)))).2)
      (realMatrixStratumNormalAction hZW hTW hN L) 0 := by
  let I : N →L[ℝ] Mat := W.subtypeL.comp N.subtypeL
  let B : Mat := A + (z : Mat)
  have heN (y : N) : e ((0, z), y) = B + I y := by rw [he]; simp [I, B]
  have hf : HasFDerivAt (fun y : N => e ((0, z), y)) I 0 := by
    simpa only [heN] using (I.hasFDerivAt (x := 0)).const_add B
  have hg : HasFDerivAt (fun C => (e.symm C).2) (realMatrixStratumNormalProjection hZW hTW hN)
      (L (e ((0, z), (0 : N)))) := by
    rw [heN, map_zero I, add_zero, hL]
    exact hasFDerivAt_realMatrixStratumChart_inverse_normal hZW hTW hN J e he hi z hz hT
  exact hg.comp 0 (L.hasFDerivAt.comp 0 hf)

end Coordinates

end Langlands
