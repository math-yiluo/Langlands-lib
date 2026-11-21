import Langlands.Representation.Archimedean.BruhatDistributionFiltration
import Langlands.Representation.Archimedean.LongestBruhatCellInvariance

/-! # Weyl-transpose invariance of an archimedean Whittaker distribution -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

open Function Set TopologicalSpace
open Langlands.Analysis Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open scoped Distributions Matrix.Norms.Operator

namespace Langlands.Archimedean

universe u

variable (F : Type u) [RCLike F] (r : ℕ)

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) F
local notation "D" => 𝓓(matrixUnitsOpen F (r + 1), ℂ)
local notation "U" => upperUnipotent (r + 1) F
local notation "τ" => matrixWeylTranspose F r

/-- The actual pullback by Weyl-conjugated transpose on matrix tests. -/
def matrixWeylTransposeTest : D →L[ℂ] D := by
  refine testLinearPullback τ ?_
  intro x hx
  obtain ⟨g, rfl⟩ := (show IsUnit x from hx)
  have h : (τ).symm g.val = τ g.val := by
    apply (τ).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, matrixWeylTranspose_involutive]
  change IsUnit ((τ).symm g.val)
  rw [h, matrixWeylTranspose_val]
  exact Units.isUnit _

@[simp]
theorem matrixWeylTransposeTest_apply (f : D) (x : M) :
    matrixWeylTransposeTest F r f x = f (τ x) := rfl

private theorem trace_matrixWeylTranspose (X : M) : (τ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, matrixWeylTranspose_entry]
  exact Equiv.sum_comp Fin.revPerm (fun i => X i i)

private theorem matrixWeylTranspose_one : τ (1 : M) = 1 := by
  ext i j
  simp [Matrix.one_apply, eq_comm]

private theorem matrixRealTracePairing_weylTranspose (X Y : M) :
    matrixRealTracePairing F (r + 1) (τ X) (τ Y) = matrixRealTracePairing F (r + 1) X Y := by
  rw [matrixRealTracePairing, ← matrixWeylTranspose_mul,
    trace_matrixWeylTranspose, Matrix.trace_mul_comm Y X]
  rfl

/-- The trace Casimir on the actual test space commutes with the transpose pullback. -/
theorem matrixTraceTestCasimir_weylTranspose (f : D) :
    matrixTraceTestCasimir F (r + 1) (matrixWeylTransposeTest F r f) =
      matrixWeylTransposeTest F r (matrixTraceTestCasimir F (r + 1) f) := by
  ext x
  by_cases hx : IsUnit x
  · obtain ⟨g, rfl⟩ := hx
    rw [matrixTraceTestCasimir_apply, matrixWeylTransposeTest_apply, matrixTraceTestCasimir_apply]
    have h : (matrixWeylTransposeTest F r f : M → ℂ) = (f : M → ℂ) ∘ τ :=
      funext (matrixWeylTransposeTest_apply F r f)
    rw [h]
    exact matrixTraceCasimir_comp_anti (τ).toLinearEquiv (matrixWeylTranspose_mul F r)
      (matrixWeylTranspose_one F r) (matrixRealTracePairing_weylTranspose F r) f.contDiff g
  · exact ((matrixTraceTestCasimir F (r + 1) (matrixWeylTransposeTest F r f)).zero_on_compl hx).trans
      ((matrixWeylTransposeTest F r (matrixTraceTestCasimir F (r + 1) f)).zero_on_compl hx).symm

/-- Scalar-Casimir distributions with the same standard Whittaker character
on both sides are invariant under Weyl-conjugated transpose. -/
theorem matrixDistribution_weylTranspose_invariant (ψ : UnitaryAdditiveCharacter F)
    (T : D →L[ℂ] ℂ) (eigenvalue : ℂ)
    (hCas : ∀ f : D, T (matrixTraceTestCasimir F (r + 1) f) = eigenvalue * T f)
    (hCov : ∀ (u v : U) (f g : D), (∀ x : M, g x = f (u.val.val * x * v.val.val)) →
      T g = ((standardCharacter ψ r u : ℂ) * (standardCharacter ψ r v : ℂ)) * T f) :
    ∀ f : D, T (matrixWeylTransposeTest F r f) = T f := by
  let P := matrixWeylTransposeTest F r
  let S := T.comp P
  have hSCas (f : D) : S (matrixTraceTestCasimir F (r + 1) f) = eigenvalue * S f := by
    change T (P (matrixTraceTestCasimir F (r + 1) f)) = eigenvalue * T (P f)
    rw [show P (matrixTraceTestCasimir F (r + 1) f) =
      matrixTraceTestCasimir F (r + 1) (P f) from (matrixTraceTestCasimir_weylTranspose F r f).symm,
      hCas]
  have hTCov (u : U) (f : D) :
      T (matrixLeftTranslateTest u.val f) = (standardCharacter ψ r u : ℂ) * T f := by
    have h := hCov u 1 f (matrixLeftTranslateTest u.val f) (fun x => by simp)
    simpa using h
  have hSCov (u : U) (f : D) :
      S (matrixLeftTranslateTest u.val f) = (standardCharacter ψ r u : ℂ) * S f := by
    let v := weylTransposeUnipotent r F u
    have hv : v.val.val = τ u.val.val := (matrixWeylTranspose_val F r u.val).symm
    have hg (x : M) :
        P (matrixLeftTranslateTest u.val f) x = P f ((1 : U).val.val * x * v.val.val) := by
      change f (u.val.val * τ x) = f (τ (1 * x * v.val.val))
      rw [one_mul, matrixWeylTranspose_mul, hv, matrixWeylTranspose_involutive]
    have h := hCov 1 v (P f) (P (matrixLeftTranslateTest u.val f)) hg
    change T (P (matrixLeftTranslateTest u.val f)) = (standardCharacter ψ r u : ℂ) * T (P f)
    simpa [v, standardCharacter_weylTranspose] using h
  have hLong (f : D) (hf : tsupport f ⊆ bruhatCellMatrixSet F (Fin.revPerm (n := r + 1))) :
      S f = T f := by
    let χ : U →* ℂ := (Units.coeHom ℂ).comp (standardCharacter ψ r)
    have hc : Continuous χ :=
      Units.continuous_val.comp (standardCharacterContinuous ψ r).continuous
    have hχ (u : U) : χ (weylTransposeUnipotent r F u) = χ u := by
      change (standardCharacter ψ r (weylTransposeUnipotent r F u) : ℂ) =
        (standardCharacter ψ r u : ℂ)
      rw [standardCharacter_weylTranspose]
    have hBW : longestBruhatCell F r ≤ matrixUnitsOpen F (r + 1) :=
      fun _ hx => isUnit_of_mem_longestBruhatCell F r hx
    have hfB : tsupport f ⊆ longestBruhatCell F r := by
      rw [bruhatCellMatrixSet_eq_image] at hf
      exact hf
    exact longestBruhatCell_transpose_invariant F r hBW T χ hc hχ hCov f (P f) hfB
      (matrixWeylTransposeTest_apply F r f)
  have hST : S = T := matrixDistribution_eq_of_agree_on_longCell ψ S T eigenvalue
    hSCas hCas hSCov hTCov hLong
  intro f
  exact DFunLike.congr_fun hST f

end Langlands.Archimedean
