import Langlands.Global.ArchimedeanRelativeAdjoint
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Alternating.Basic

/-! # Compact adjoint curve differentiation in actual matrix coordinates -/

noncomputable section

universe u v

open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

private theorem realMultilinear_continuous
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : ℕ)
    (f : MultilinearMap ℝ (fun _ : Fin q => E) ℂ) : Continuous f := by
  let b := Module.finBasis ℝ E
  have he : (fun x => f x) = (fun x =>
      ∑ a : Fin q → Fin (Module.finrank ℝ E),
        (∏ i, b.repr (x i) (a i)) • f (fun i => b (a i))) := by
    funext x
    calc
      f x = f (fun i => ∑ a, b.repr (x i) a • b a) := by
        congr 1
        funext i
        exact (b.sum_repr (x i)).symm
      _ = _ := by rw [f.map_sum]; simp_rw [f.map_smul_univ]
  change Continuous (fun x => f x)
  rw [he]
  apply continuous_finsetSum
  intro a _
  have hs : Continuous (fun x : Fin q → E => ∏ i, b.repr (x i) (a i)) := by
    apply continuous_finsetProd
    intro i _
    exact (b.coord (a i)).continuous_of_finiteDimensional.comp (continuous_apply i)
  exact hs.smul continuous_const

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Differentiate actual compact conjugation in the mixed matrix coordinates. -/
theorem compactCurve_adjoint_deriv (Y : compactLieSubalgebra K n)
    (X : RealLieAlgebra K n) (c : ℝ → standardInfiniteCompact K n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt (fun t => (archimedeanGLCoordinates K n (c t).val).val)
      (realLieAlgebraToMatrix K n Y.val) 0) :
    HasDerivAt
      (fun t => realLieAlgebraToMatrix K n (realLieConjugation K n (c t).val X))
      (realLieAlgebraToMatrix K n ⁅Y.val, X⁆) 0 := by
  have hstar :
      star (realLieAlgebraToMatrix K n Y.val) =
        -realLieAlgebraToMatrix K n Y.val :=
    congrArg (realLieAlgebraToMatrix K n)
      ((mem_compactLieSubalgebra K n Y.val).mp Y.property)
  have h := (hc.mul_const (realLieAlgebraToMatrix K n X)).mul hc.star
  have h0 : (archimedeanGLCoordinates K n (c 0).val).val = 1 := by
    simp [hc0]
  simp only [h0, star_one, mul_one, one_mul, hstar, mul_neg, ← sub_eq_add_neg,
    ← realLieAlgebraToMatrix_lie] at h
  have he :
      (fun t => realLieAlgebraToMatrix K n (realLieConjugation K n (c t).val X)) =
        (fun t => (archimedeanGLCoordinates K n (c t).val).val *
          realLieAlgebraToMatrix K n X *
          star (archimedeanGLCoordinates K n (c t).val).val) := by
    funext t
    rw [realLieAlgebraToMatrix_realLieConjugation, map_inv,
      standardCompact_coordinates_star]
  rw [he]
  exact h

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Scalar evaluation of an algebraic complex cochain, in actual matrix
coordinates, bundled as a continuous real multilinear map. -/
def scalarCochainMatrixEvaluation (q : ℕ)
    (f : (ComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V) (ℓ : V →ₗ[ℂ] ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => ArchimedeanMatrix K n) ℂ :=
  let a := ((ℓ.compMultilinearMap f.toMultilinearMap).restrictScalars ℝ).compLinearMap
    (fun _ => (complexify K n).toLinearMap.comp
      (realLieAlgebraToMatrix K n).symm.toLinearMap)
  { a with cont := realMultilinear_continuous q a }

@[simp]
theorem scalarCochainMatrixEvaluation_apply (q : ℕ)
    (f : (ComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V) (ℓ : V →ₗ[ℂ] ℂ)
    (X : Fin q → ArchimedeanMatrix K n) :
    scalarCochainMatrixEvaluation K n q f ℓ X =
      ℓ (f (fun i => complexify K n ((realLieAlgebraToMatrix K n).symm (X i)))) := rfl

/-- The scalar cochain derivative along actual compact adjoint curves is the
sum of insertions of the commutator in each argument. -/
theorem compactCurve_scalarCochain_deriv (q : ℕ)
    (f : (ComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V) (ℓ : V →ₗ[ℂ] ℂ)
    (Y : compactLieSubalgebra K n) (X : Fin q → RealLieAlgebra K n)
    (c : ℝ → standardInfiniteCompact K n) (hc0 : c 0 = 1)
    (hc : HasDerivAt (fun t => (archimedeanGLCoordinates K n (c t).val).val)
      (realLieAlgebraToMatrix K n Y.val) 0) :
    HasDerivAt
      (fun t => ℓ (f (fun i =>
        complexify K n (realLieConjugation K n (c t).val (X i)))))
      (∑ i, ℓ (f (Function.update (fun j => complexify K n (X j)) i
        (complexify K n ⁅Y.val, X i⁆)))) 0 := by
  let A := scalarCochainMatrixEvaluation K n q f ℓ
  have ht := hasDerivAt_pi.mpr
    (fun i => compactCurve_adjoint_deriv K n Y (X i) c hc0 hc)
  have h0 : (fun i => realLieAlgebraToMatrix K n (X i)) =
      (fun i => realLieAlgebraToMatrix K n
        (realLieConjugation K n (c 0).val (X i))) := by
    simp [hc0, realLieConjugation_one]
  have h := (A.hasFDerivAt (fun i => realLieAlgebraToMatrix K n (X i))).comp_hasDerivAt_of_eq
    0 ht h0
  have hd : A.linearDeriv (fun i => realLieAlgebraToMatrix K n (X i))
      (fun i => realLieAlgebraToMatrix K n ⁅Y.val, X i⁆) =
      ∑ i, ℓ (f (Function.update (fun j => complexify K n (X j)) i
        (complexify K n ⁅Y.val, X i⁆))) := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    apply Finset.sum_congr rfl
    intro i _
    change ℓ (f (fun j => complexify K n
      ((realLieAlgebraToMatrix K n).symm
        (Function.update (fun k => realLieAlgebraToMatrix K n (X k)) i
          (realLieAlgebraToMatrix K n ⁅Y.val, X i⁆) j)))) = _
    congr 2
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, LinearEquiv.symm_apply_apply]
    · simp only [Function.update_of_ne hj, LinearEquiv.symm_apply_apply]
  rw [hd] at h
  simpa only [Function.comp_def, A, scalarCochainMatrixEvaluation_apply,
    LinearEquiv.symm_apply_apply] using h

end Langlands.Global.ArchimedeanGL
