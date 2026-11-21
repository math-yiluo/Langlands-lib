import Langlands.Group.GL.BruhatMatrixCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.RCLike.Lemmas

/-! # The differential of the local product along a Bruhat cell -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open scoped ContDiff Matrix.Norms.Operator RightActions

namespace Langlands.GeneralLinear

universe u

variable {F : Type u} [RCLike F] {n : ℕ} {w : Equiv.Perm (Fin n)}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "B" => upperTriangularSubgroup n F
local notation "T" => (bruhatUpperSpace F n × bruhatInversionSpace F w)
local notation "N" => bruhatNormalSpace F w

/-- The two tangent factors based at `b * p`. For a Bruhat chart the
right factor `p` is the permutation matrix times the unipotent factor. -/
def bruhatCellMatrixParam (b : B) (p : Mˣ) (z : T) : M :=
  b.val.val * (1 + z.1.val) * (1 + z.2.val) * p.val

@[simp]
theorem bruhatCellMatrixParam_zero (b : B) (p : Mˣ) :
    bruhatCellMatrixParam (w := w) b p 0 = b.val.val * p.val := by
  simp [bruhatCellMatrixParam]

private def upperCoordinate : T →L[ℝ] M :=
  ((bruhatUpperSpace F n).subtypeL.restrictScalars ℝ).comp
    (ContinuousLinearMap.fst ℝ (bruhatUpperSpace F n) (bruhatInversionSpace F w))

private def inversionCoordinate : T →L[ℝ] M :=
  ((bruhatInversionSpace F w).subtypeL.restrictScalars ℝ).comp
    (ContinuousLinearMap.snd ℝ (bruhatUpperSpace F n) (bruhatInversionSpace F w))

theorem contDiff_bruhatCellMatrixParam (b : B) (p : Mˣ) :
    ContDiff ℝ ∞ (bruhatCellMatrixParam (w := w) b p) := by
  have hu : ContDiff ℝ ∞ (fun z : T => (1 : M) + upperCoordinate z) :=
    contDiff_const.add (upperCoordinate (F := F) (w := w)).contDiff
  have hr : ContDiff ℝ ∞ (fun z : T => (1 : M) + inversionCoordinate z) :=
    contDiff_const.add (inversionCoordinate (F := F) (w := w)).contDiff
  have hb : ContDiff ℝ ∞ (fun _ : T => b.val.val) := contDiff_const
  have hp : ContDiff ℝ ∞ (fun _ : T => p.val) := contDiff_const
  change ContDiff ℝ ∞ (fun z : T =>
    b.val.val * (1 + upperCoordinate z) * (1 + inversionCoordinate z) * p.val)
  exact ((hb.mul hu).mul hr).mul hp

/-- The real derivative of the tangent product at zero. -/
def bruhatCellMatrixDifferential (b : B) (p : Mˣ) : T →L[ℝ] M :=
  (ContinuousLinearMap.mulLeftRight ℝ M b.val.val p.val).comp
    (upperCoordinate + inversionCoordinate)

theorem bruhatCellMatrixDifferential_apply (b : B) (p : Mˣ) (z : T) :
    bruhatCellMatrixDifferential b p z = b.val.val * (z.1.val + z.2.val) * p.val :=
  rfl

theorem hasFDerivAt_bruhatCellMatrixParam (b : B) (p : Mˣ) :
    HasFDerivAt (bruhatCellMatrixParam (w := w) b p) (bruhatCellMatrixDifferential b p) 0 := by
  have hu := (upperCoordinate (F := F) (w := w)).hasFDerivAt (x := 0)
  have hr := (inversionCoordinate (F := F) (w := w)).hasFDerivAt (x := 0)
  have hp := (((hu.const_add (1 : M)).const_mul b.val.val).mul'
    (hr.const_add (1 : M))).mul_const' p.val
  let u : T →L[ℝ] M := upperCoordinate
  let r : T →L[ℝ] M := inversionCoordinate
  change HasFDerivAt (fun z : T => b.val.val * (1 + u z) * (1 + r z) * p.val)
    ((ContinuousLinearMap.mulLeftRight ℝ M b.val.val p.val).comp (u + r)) 0
  have he : (ContinuousLinearMap.mulLeftRight ℝ M b.val.val p.val).comp (u + r) =
      ((b.val.val * (1 + u 0)) •> r + b.val.val •> u <• (1 + r 0)) <• p.val := by
    apply ContinuousLinearMap.ext
    intro z
    change b.val.val * (u z + r z) * p.val =
      (b.val.val * (1 + u 0) * r z + b.val.val * u z * (1 + r 0)) * p.val
    simp only [map_zero, add_zero, mul_one, mul_add]
    rw [add_comm (b.val.val * u z)]
  rw [he]
  exact hp

/-- The invertible derivative in the tangent and normal matrix coordinates. -/
def bruhatTransverseDifferential (b : B) (p : Mˣ) : (T × N) ≃L[ℝ] M := by
  haveI : FiniteDimensional ℝ (T × N) := FiniteDimensional.trans ℝ F (T × N)
  haveI : FiniteDimensional ℝ M := FiniteDimensional.trans ℝ F M
  exact (((bruhatConjugatedMatrixCoordinates w b).restrictScalars ℝ).trans
    ((b.val.mulLeftLinearEquiv ℝ M).trans (p.mulRightLinearEquiv ℝ))).toContinuousLinearEquiv

theorem bruhatTransverseDifferential_apply (b : B) (p : Mˣ) (z : T × N) :
    bruhatTransverseDifferential b p z =
      z.2.val * (b.val.val * p.val) + b.val.val * (z.1.1.val + z.1.2.val) * p.val := by
  change b.val.val *
    ((b⁻¹ : B).val.val * z.2.val * b.val.val + z.1.1.val + z.1.2.val) * p.val = _
  have hb : b.val.val * (b⁻¹ : B).val.val = 1 := b.val.val_inv
  have hc : b.val.val * ((b⁻¹ : B).val.val * z.2.val * b.val.val) =
      z.2.val * b.val.val := by
    simp only [← mul_assoc, hb, one_mul]
  rw [add_assoc, mul_add, hc, add_mul, mul_assoc z.2.val]

end Langlands.GeneralLinear
