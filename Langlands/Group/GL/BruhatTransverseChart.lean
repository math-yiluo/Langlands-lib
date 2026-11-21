import Langlands.Analysis.ExponentialProductCoordinates
import Langlands.Group.GL.BruhatMatrixChartDifferential
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Straightening a transverse matrix field along a Bruhat chart -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open scoped ContDiff Matrix.Norms.Operator
open Langlands.Analysis

namespace Langlands.GeneralLinear

universe u

variable {F : Type u} [RCLike F] {n : ℕ} {w : Equiv.Perm (Fin n)}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "B" => upperTriangularSubgroup n F
local notation "T" => (bruhatUpperSpace F n × bruhatInversionSpace F w)
local notation "Nspace" => bruhatNormalSpace F w
local notation "W[" S "]" => (T × (↥S) × ℝ)

private theorem exists_bruhatNormalCoordinate {X : Nspace} (hX : X ≠ 0) :
    ∃ h : Nspace →L[ℝ] ℝ, h X = 1 := by
  have hnorm : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ X hnorm
  refine ⟨‖X‖⁻¹ • g, ?_⟩
  change ‖X‖⁻¹ * g X = 1
  rw [hg]
  exact inv_mul_cancel₀ hnorm

private theorem exists_bruhatNormalSplit {X : Nspace} (hX : X ≠ 0) :
    ∃ S : Submodule ℝ Nspace, ∃ J : (↥S × ℝ) ≃ₗ[ℝ] Nspace,
      ∀ z, J z = z.2 • X + z.1.val := by
  obtain ⟨h, hh⟩ := exists_bruhatNormalCoordinate (F := F) (w := w) hX
  let S := (h : Nspace →ₗ[ℝ] ℝ).ker
  let s : ℝ →L[ℝ] Nspace := (ContinuousLinearMap.id ℝ ℝ).smulRight X
  have hs : Function.RightInverse s h := by
    intro t
    change h (t • X) = t
    rw [map_smul, hh, smul_eq_mul, mul_one]
  let e : Nspace ≃L[ℝ] ℝ × S := ContinuousLinearEquiv.equivOfRightInverse h s hs
  let J := (ContinuousLinearEquiv.prodComm ℝ S ℝ).trans e.symm
  exact ⟨S, J.toLinearEquiv, fun _ => rfl⟩

private def normalInclusion (S : Submodule ℝ Nspace) : S →L[ℝ] M :=
  ((bruhatNormalSpace F w).subtypeL.restrictScalars ℝ).comp S.subtypeL

/-- The full matrix product with the chosen transverse field in the
last real coordinate. -/
abbrev bruhatStraightenedMatrixParam (S : Submodule ℝ Nspace)
    (b : B) (p : Mˣ) (X : Nspace) : W[S] → M :=
  exponentialProduct (E := T) (N := ↥S) (A := M)
    X.val (normalInclusion (F := F) (w := w) S) (bruhatCellMatrixParam (w := w) b p)

@[simp]
theorem bruhatStraightenedMatrixParam_slice (S : Submodule ℝ Nspace)
    (b : B) (p : Mˣ) (X : Nspace) (z : T) :
    bruhatStraightenedMatrixParam (F := F) (w := w) S b p X (z, 0, 0) =
      bruhatCellMatrixParam (w := w) b p z := by
  simp [bruhatStraightenedMatrixParam, exponentialProduct, exponentialNormalFactor]

theorem contDiff_bruhatStraightenedMatrixParam (S : Submodule ℝ Nspace)
    (b : B) (p : Mˣ) (X : Nspace) :
    ContDiff ℝ ∞ (bruhatStraightenedMatrixParam (F := F) (w := w) S b p X) := by
  have h := contDiff_exponentialProduct (E := T) (N := ↥S) (A := M)
    (b := bruhatCellMatrixParam (w := w) b p)
    X.val (normalInclusion (F := F) (w := w) S) (contDiff_bruhatCellMatrixParam (w := w) b p)
  exact h

private theorem exists_bruhatStraightenedChart_of_split (S : Submodule ℝ Nspace)
    (b : B) (p : Mˣ) (X : Nspace) (J : (↥S × ℝ) ≃ₗ[ℝ] Nspace)
    (hJ : ∀ z, J z = z.2 • X + z.1.val) :
    ∃ e : OpenPartialHomeomorph W[S] M,
      (e : W[S] → M) = bruhatStraightenedMatrixParam (F := F) (w := w) S b p X ∧
      0 ∈ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have : FiniteDimensional ℝ T := FiniteDimensional.trans ℝ F T
  have : FiniteDimensional ℝ Nspace := FiniteDimensional.trans ℝ F Nspace
  have : FiniteDimensional ℝ M := FiniteDimensional.trans ℝ F M
  let D := bruhatTransverseDifferential (w := w) b p
  let L : W[S] ≃ₗ[ℝ] M := ((LinearEquiv.refl ℝ T).prodCongr J).trans D.toLinearEquiv
  apply exists_exponentialProductChart (E := T) (N := ↥S) (A := M)
    (b := bruhatCellMatrixParam (w := w) b p)
    X.val (normalInclusion (F := F) (w := w) S) (contDiff_bruhatCellMatrixParam (w := w) b p) L
  intro z
  change D (z.1, J z.2) = _
  rw [bruhatTransverseDifferential_apply, (hasFDerivAt_bruhatCellMatrixParam (w := w) b p).fderiv,
    bruhatCellMatrixDifferential_apply, bruhatCellMatrixParam_zero, hJ]
  exact add_comm _ _

/-- A nonzero normal matrix gives an open chart with a smooth local inverse. -/
theorem exists_bruhatStraightenedChart (b : B) (p : Mˣ) (X : Nspace) (hX : X ≠ 0) :
    ∃ S : Submodule ℝ Nspace, ∃ e : OpenPartialHomeomorph W[S] M,
      (e : W[S] → M) = bruhatStraightenedMatrixParam (F := F) (w := w) S b p X ∧
      0 ∈ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨S, J, hJ⟩ := exists_bruhatNormalSplit (F := F) (w := w) hX
  exact ⟨S, exists_bruhatStraightenedChart_of_split (F := F) (w := w) S b p X J hJ⟩

/-- In chart coordinates the field `x ↦ X * x` is the derivative
in the last coordinate, at every point of the parameter space. -/
theorem fderiv_bruhatStraightenedMatrixParam_last (S : Submodule ℝ Nspace)
    (b : B) (p : Mˣ) (X : Nspace) (z : W[S]) :
    fderiv ℝ (bruhatStraightenedMatrixParam (F := F) (w := w) S b p X) z (0, 0, 1) =
      X.val * bruhatStraightenedMatrixParam (F := F) (w := w) S b p X z := by
  have h := fderiv_exponentialProduct_last (E := T) (N := ↥S) (A := M)
    (b := bruhatCellMatrixParam (w := w) b p)
    X.val (normalInclusion (F := F) (w := w) S) (contDiff_bruhatCellMatrixParam (w := w) b p) z
  exact h

end Langlands.GeneralLinear
