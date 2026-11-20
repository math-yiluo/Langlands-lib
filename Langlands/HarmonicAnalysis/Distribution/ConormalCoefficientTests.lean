import Langlands.Analysis.SymmetricCovectorPowers
import Langlands.LinearAlgebra.RealSpectralConormalInvariance
import Mathlib.Analysis.Distribution.TestFunction

/-! # Pure powers as tests for conormal coefficient functionals -/

noncomputable section

open TopologicalSpace Matrix
open scoped Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

namespace Langlands.HarmonicAnalysis

variable {E G F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup N] [NormedSpace ℝ N] {U : Opens E}

/-- A scalar test multiplied by a constant coefficient vector. -/
def scalarTimesVectorTest (f : 𝓓(U, ℝ)) (v : G) : 𝓓(U, G) :=
  TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight v) f

@[simp]
theorem scalarTimesVectorTest_apply (f : 𝓓(U, ℝ)) (v : G) (x : E) :
    scalarTimesVectorTest f v x = f x • v := rfl

/-- The coefficient-vector argument varies continuously in the test space in finite dimension. -/
theorem continuous_scalarTimesVectorTest [FiniteDimensional ℝ G] (f : 𝓓(U, ℝ)) :
    Continuous (scalarTimesVectorTest (G := G) f) := by
  let L : G →ₗ[ℝ] 𝓓(U, G) :=
    { toFun := scalarTimesVectorTest f
      map_add' := fun v w => by ext x; simp [smul_add]
      map_smul' := fun c v => by ext x; simp [smul_comm c (f x)] }
  exact L.continuous_of_finiteDimensional

/-- A test with a constant pure covector power and a scalar coefficient. -/
def pureCovectorPowerTest (i : ℕ) (f : 𝓓(U, ℝ)) (covector : N →L[ℝ] ℝ) :
    𝓓(U, N [×i]→L[ℝ] ℝ) :=
  scalarTimesVectorTest f (continuousCovectorPower i covector)

@[simp]
theorem pureCovectorPowerTest_apply (i : ℕ) (f : 𝓓(U, ℝ)) (covector : N →L[ℝ] ℝ) (x : E) :
    pureCovectorPowerTest i f covector x = f x • continuousCovectorPower i covector := rfl

private theorem finiteDimensional_continuousMultilinearForms [FiniteDimensional ℝ N] (i : ℕ) :
    FiniteDimensional ℝ (N [×i]→L[ℝ] ℝ) := by
  let b := Module.finBasis ℝ N
  let B := Basis.multilinearMap (R := ℝ) (fun _ : Fin i => b) (Module.finBasis ℝ ℝ)
  let := Module.Finite.of_basis B
  exact FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

theorem continuous_pureCovectorPowerTest [FiniteDimensional ℝ N] (i : ℕ) (f : 𝓓(U, ℝ)) :
    Continuous (pureCovectorPowerTest (N := N) i f) := by
  let : FiniteDimensional ℝ (N [×i]→L[ℝ] ℝ) := finiteDimensional_continuousMultilinearForms i
  exact (continuous_scalarTimesVectorTest f).comp (continuous_continuousCovectorPower i)

/-- A linear functional that kills scalar tests times pure powers kills every pointwise symmetric
coefficient test. -/
theorem eval_symmetricTest_eq_zero_of_pureCovectorPowerTest
    [FiniteDimensional ℝ N] {i : ℕ} (C : 𝓓(U, N [×i]→L[ℝ] ℝ) →L[ℝ] F)
    (hC : ∀ (f : 𝓓(U, ℝ)) (covector : N →L[ℝ] ℝ), C (pureCovectorPowerTest i f covector) = 0)
    (a : 𝓓(U, N [×i]→L[ℝ] ℝ))
    (ha : ∀ (x : E) (v : Fin i → N) (σ : Equiv.Perm (Fin i)), a x (v ∘ σ) = a x v) :
    C a = 0 := by
  obtain ⟨d, cov, coord, hexp⟩ := exists_continuousCovectorPower_expansion (E := N) i
  let f (k : Fin d) : 𝓓(U, ℝ) := TestFunction.postcompCLM (coord k) a
  have he : a = ∑ k : Fin d, pureCovectorPowerTest i (f k) (cov k) := by
    apply TestFunction.ext
    intro x
    have h := hexp (a x) (fun σ v => ha x v σ)
    simpa only [_root_.sum_apply, pureCovectorPowerTest_apply, f, TestFunction.postcompCLM_apply,
      Function.comp_apply] using h
  rw [he, map_sum]
  simp [hC]

section Matrix

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A

/-- On a real spectral stratum normal space, stabilizer invariance and adjusted transpose
oddness of all pure-power coefficient tests force the symmetric leading coefficient to vanish. -/
theorem realMatrixStratum_symmetricCoefficient_eq_zero
    {A : Mat} {W : Submodule ℝ Mat} {N₀ : Submodule ℝ W}
    (hZW : Z[A] ≤ W) (hTW : IsCompl T[A] W) (hN : IsCompl (Z[A].comap W.subtype) N₀)
    {i : ℕ} (C : 𝓓(U, (↥N₀) [×i]→L[ℝ] ℝ) →L[ℝ] F)
    {q : Matˣ} (hq : q.val * A * q.inv = Aᵀ)
    (hconj : ∀ (u : Matˣ), Commute (u : Mat) A → ∀ (f : 𝓓(U, ℝ)) (covector : N₀ →L[ℝ] ℝ),
      C (pureCovectorPowerTest i f (covector.comp (realMatrixStratumStabilizerNormalAction hZW hTW hN u))) =
        C (pureCovectorPowerTest i f covector))
    (hodd : ∀ (f : 𝓓(U, ℝ)) (covector : N₀ →L[ℝ] ℝ),
      C (pureCovectorPowerTest i f (covector.comp (realMatrixStratumAdjustedTransposeNormalAction hZW hTW hN q))) =
        -C (pureCovectorPowerTest i f covector))
    (a : 𝓓(U, (↥N₀) [×i]→L[ℝ] ℝ))
    (ha : ∀ (x : E) (v : Fin i → N₀) (σ : Equiv.Perm (Fin i)), a x (v ∘ σ) = a x v) :
    C a = 0 := by
  apply eval_symmetricTest_eq_zero_of_pureCovectorPowerTest C _ a ha
  intro f covector
  let p : (N₀ →L[ℝ] ℝ) → F := fun cov => C (pureCovectorPowerTest i f cov)
  have hp : Continuous p := C.continuous.comp (continuous_pureCovectorPowerTest i f)
  have h := realMatrixStratumNormalDual_transpose_invariant hZW hTW hN p hp
    (fun u hu v => hconj u hu f v) hq covector
  have hneg : C (pureCovectorPowerTest i f covector) = -C (pureCovectorPowerTest i f covector) :=
    h.symm.trans (hodd f covector)
  let v := C (pureCovectorPowerTest i f covector)
  have hz : (2 : ℝ) • v = 0 := by
    rw [two_smul]
    calc
      v + v = v + (-v) := congrArg (v + ·) hneg
      _ = 0 := add_neg_cancel v
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end Matrix

end Langlands.HarmonicAnalysis
