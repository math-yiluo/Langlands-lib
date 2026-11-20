import Langlands.Representation.Archimedean.RealLeviLimit
import Langlands.Representation.Archimedean.RealSignedOrthogonalDifferential

/-! # Transverse derivatives in real Levi coordinates -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator ContDiff

namespace Langlands.Archimedean.RealLeviCartanDifferential

open GramFormula PrincipalSeriesExtension RealSignedOrthogonalDifferential RealLeviChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "Mat" k:max => Matrix (Fin k) (Fin k) ℝ

section Matrix

variable {n : ℕ}

theorem eq_of_skew_of_lower_eq {A B : Mat n} (hA : Aᵀ = -A) (hB : Bᵀ = -B)
    (h : ∀ i j : Fin n, j < i → A i j = B i j) : A = B := by
  have ha (i j : Fin n) : A j i = -A i j := congrArg (fun M : Mat n => M i j) hA
  have hb (i j : Fin n) : B j i = -B i j := congrArg (fun M : Mat n => M i j) hB
  ext i j
  rcases lt_trichotomy j i with hlt | heq | hgt
  · exact h i j hlt
  · subst j
    linarith only [ha i i, hb i i]
  · rw [ha j i, hb j i, h j i hgt]

private def transposeCLM (n : ℕ) : Mat n →L[ℝ] Mat n :=
  (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap.toContinuousLinearMap

private theorem signedOrthogonal_one (n : ℕ) : signedOrthogonal (1 : Mat n) = 1 := by
  have h := signedOrthogonal_mul (b := (1 : Mat n)) (κ := 1)
    Matrix.blockTriangular_one (fun _ => by simp) (by simp)
  simpa [signReal] using h

end Matrix

section Lower

variable {c : ℕ} (sz : Fin c → ℕ)

local notation "N" => ∑ i, sz i
local notation "XSpace" => (Coord sz → ℝ)

private def strictCLM : XSpace →L[ℝ] Mat N :=
  ({ toFun := strict (sz := sz)
     map_add' := fun X Y => by
       ext i j
       simp only [strict, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
       split_ifs <;> simp
     map_smul' := fun a X => by
       ext i j
       simp only [strict, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
       split_ifs <;> simp } : XSpace →ₗ[ℝ] Mat N).toContinuousLinearMap

/-- Embed the lower off-block entries as a skew-symmetric matrix. -/
def transverseSkew : XSpace →L[ℝ] Mat N :=
  strictCLM sz - (transposeCLM N).comp (strictCLM sz)

theorem transverseSkew_apply (X : XSpace) :
    transverseSkew sz X = strict (sz := sz) X - (strict (sz := sz) X)ᵀ := rfl

theorem transverseSkew_transpose (X : XSpace) :
    (transverseSkew sz X)ᵀ = -(transverseSkew sz X) := by
  rw [transverseSkew_apply, Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub]

theorem transverseSkew_apply_of_lt (X : XSpace) {i j : Fin N} (hij : j < i) :
    transverseSkew sz X i j = strict (sz := sz) X i j := by
  rw [transverseSkew_apply, Matrix.sub_apply, Matrix.transpose_apply,
    strict_apply_of_not_lt X (not_lt_of_ge (cls_mono sz hij.le)), sub_zero]

/-- Scale a lower coordinate by the column radius divided by the row radius. -/
def radialScale (d : Fin N → ℝ) : XSpace →L[ℝ] XSpace :=
  ({ toFun := fun X ij => d ij.1.2 / d ij.1.1 * X ij
     map_add' := fun _ _ => funext fun _ => mul_add _ _ _
     map_smul' := fun _ _ => funext fun _ => mul_left_comm _ _ _
   } : XSpace →ₗ[ℝ] XSpace).toContinuousLinearMap

@[simp]
theorem radialScale_apply (d : Fin N → ℝ) (X : XSpace) (ij : Coord sz) :
    radialScale sz d X ij = d ij.1.2 / d ij.1.1 * X ij := rfl

private theorem strict_radialScale (d : Fin N → ℝ) (X : XSpace) (i j : Fin N) :
    strict (sz := sz) (radialScale sz d X) i j = (d j / d i) * strict (sz := sz) X i j := by
  simp only [strict, Matrix.of_apply]
  split_ifs <;> simp

theorem contDiff_lower_matrix : ContDiff ℝ ∞ (lower sz) := by
  have he : lower sz = fun X : XSpace => strictCLM sz X + 1 :=
    funext (lower_eq_strict_add_one (sz := sz))
  rw [he]
  exact (strictCLM sz).contDiff.add contDiff_const

private theorem hasFDerivAt_lower_matrix :
    HasFDerivAt (lower sz) (strictCLM sz) 0 := by
  have he : lower sz = fun X : XSpace => strictCLM sz X + 1 :=
    funext (lower_eq_strict_add_one (sz := sz))
  rw [he]
  exact (strictCLM sz).hasFDerivAt.add_const 1

theorem contDiff_signedOrthogonal_lower :
    ContDiff ℝ ∞ (fun X : XSpace => signedOrthogonal (lower sz X)) := by
  rw [contDiff_iff_contDiffAt]
  intro X
  have hX : IsUnit (lower sz X) := by
    rw [← lowerGL_val]
    exact (lowerGL sz X).isUnit
  exact (contDiffAt_signedOrthogonal hX).comp X (contDiff_lower_matrix sz).contDiffAt

@[simp]
theorem signedOrthogonal_lower_zero : signedOrthogonal (lower sz (0 : XSpace)) = 1 := by
  rw [RealLeviLimit.lower_zero, signedOrthogonal_one]

theorem hasFDerivAt_signedOrthogonal_lower :
    HasFDerivAt (fun X : XSpace => signedOrthogonal (lower sz X)) (transverseSkew sz) 0 := by
  have h := realSignedOrthogonalDifferential N (fun _ => 1) (fun _ => one_pos)
  simp only [Matrix.diagonal_one, div_one] at h
  let D := fderiv ℝ (signedOrthogonal (n := N)) 1
  have hD : HasFDerivAt signedOrthogonal D (lower sz (0 : XSpace)) := by
    rw [RealLeviLimit.lower_zero]
    exact (h.1.differentiableAt (by simp)).hasFDerivAt
  have hc := hD.comp 0 (hasFDerivAt_lower_matrix sz)
  refine hc.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro X
  change D (strict (sz := sz) X) = transverseSkew sz X
  have hDX := h.2 (strict (sz := sz) X)
  exact eq_of_skew_of_lower_eq hDX.1 (transverseSkew_transpose sz X) fun i j hij => by
    rw [hDX.2 i j hij, transverseSkew_apply_of_lt sz X hij]

/-- The radial part of the transverse derivative in the opposed coordinates.
Here the orthogonal factor of a lower chart is multiplied by a positive
diagonal before taking its orthogonal factor again. -/
def RealLeviCartanDifferentialStatement (c : ℕ) (sz : Fin c → ℕ) : Prop :=
  ∀ (d : Fin (∑ i, sz i) → ℝ), (∀ i, 0 < d i) →
    ContDiffAt ℝ ∞
      (fun X : Coord sz → ℝ => signedOrthogonal (signedOrthogonal (lower sz X) * diagonal d)) 0 ∧
    HasFDerivAt
      (fun X : Coord sz → ℝ => signedOrthogonal (signedOrthogonal (lower sz X) * diagonal d))
      ((transverseSkew sz).comp (radialScale sz d)) 0

theorem realLeviCartanDifferential : RealLeviCartanDifferentialStatement c sz := by
  intro d hd
  let F (X : XSpace) := signedOrthogonal (lower sz X) * diagonal d
  have hF0 : F 0 = diagonal d := by simp [F]
  have h := realSignedOrthogonalDifferential N d hd
  have hD : ContDiffAt ℝ ∞ signedOrthogonal (F 0) := by rw [hF0]; exact h.1
  have hF : ContDiffAt ℝ ∞ F 0 :=
    (contDiff_signedOrthogonal_lower sz).contDiffAt.mul contDiffAt_const
  refine ⟨hD.comp 0 hF, ?_⟩
  let D := fderiv ℝ (signedOrthogonal (n := N)) (diagonal d)
  have hder : HasFDerivAt signedOrthogonal D (F 0) := by
    rw [hF0]
    exact (h.1.differentiableAt (by simp)).hasFDerivAt
  have hc := hder.comp 0 ((hasFDerivAt_signedOrthogonal_lower sz).mul_const' (diagonal d))
  refine hc.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro X
  change D (transverseSkew sz X * diagonal d) = transverseSkew sz (radialScale sz d X)
  have hDX := h.2 (transverseSkew sz X * diagonal d)
  apply eq_of_skew_of_lower_eq hDX.1 (transverseSkew_transpose sz (radialScale sz d X))
  intro i j hij
  rw [hDX.2 i j hij, Matrix.mul_diagonal, transverseSkew_apply_of_lt sz X hij,
    transverseSkew_apply_of_lt sz (radialScale sz d X) hij, strict_radialScale sz d X i j]
  ring

end Lower

end Langlands.Archimedean.RealLeviCartanDifferential
