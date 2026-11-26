import Langlands.BaseChange.OrbitChartDerivative
import Mathlib.Analysis.Normed.Ring.Units

/-! # Strict differentiation with a varying norm lift -/

noncomputable section

open scoped RightActions

namespace Langlands.BaseChange

universe u v w z

variable {F : Type u} [NontriviallyNormedField F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R]
  {S : Type w} [NormedAddCommGroup S]
  {W : Type z} [NormedAddCommGroup W] [NormedSpace F W]

/-- The normalized twisted orbit chart with a varying lift in the torus coordinate. -/
def twistedOrbitAffineChart (A : R →L[F] R) (j : W →L[F] R) (f : S → R)
    (x : S × W) : R := Ring.inverse (1 + j x.2) * f x.1 * (1 + A (j x.2)) - 1

@[simp]
theorem twistedOrbitAffineChart_zero (A : R →L[F] R) (j : W →L[F] R) {f : S → R}
    (hf : f 0 = 1) : twistedOrbitAffineChart A j f 0 = 0 := by
  simp [twistedOrbitAffineChart, hf]

variable [NormedSpace F S] [HasSummableGeomSeries R]

/-- On the transverse coordinate the derivative subtracts the identity from
 the twisted adjoint. On the torus coordinate it is the derivative of the lift. -/
theorem hasStrictFDerivAt_twistedOrbitAffineChart
    (A : R →L[F] R) (j : W →L[F] R) {f : S → R} (hf : f 0 = 1)
    {s : S →L[F] R} (hs : HasStrictFDerivAt f s 0) :
    HasStrictFDerivAt (twistedOrbitAffineChart A j f)
      (s.comp (ContinuousLinearMap.fst F S W) +
        (A - ContinuousLinearMap.id F R).comp (j.comp (ContinuousLinearMap.snd F S W))) 0 := by
  let J := j.comp (ContinuousLinearMap.snd F S W)
  have hJ := J.hasStrictFDerivAt (x := 0) |>.const_add (c := (1 : R))
  have hInv : HasStrictFDerivAt (Ring.inverse : R → R) (-ContinuousLinearMap.id F R)
      (1 + J 0) := by
    rw [map_zero, add_zero]
    convert hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Rˣ) using 1
    ext x
    simp [ContinuousLinearMap.mulLeftRight_apply]
  let P := ContinuousLinearMap.fst F S W
  have hP : HasStrictFDerivAt (fun x => f (P x)) (s.comp P) 0 :=
    hs.comp 0 P.hasStrictFDerivAt
  have hA := (A.comp J).hasStrictFDerivAt (x := 0) |>.const_add (c := (1 : R))
  have h := (((hInv.comp 0 hJ).mul' hP).mul' hA).sub_const (1 : R)
  change HasStrictFDerivAt (twistedOrbitAffineChart A j f) _ 0 at h
  convert h using 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [P, J, map_zero, add_zero, Ring.inverse_one, hf,
    one_mul, mul_one, _root_.smul_apply, _root_.add_apply,
    _root_.sub_apply, _root_.neg_apply, smul_eq_mul, op_smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, Pi.mul_apply]
  abel

end Langlands.BaseChange
