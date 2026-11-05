import Langlands.Geometry.Manifold.VectorFieldCommutatorStatement

/-! # Scalar differential commutators on manifolds -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompleteSpace E] [I.Boundaryless]

omit [CompleteSpace E] in
private lemma scalarDerivative_in_chart (f : M → ℂ) (x : M) :
    mvfderiv I f x =
      fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℂ) f x
  · simpa [I.range_eq_univ, writtenInExtChartAt, chartAt_self_eq] using hf.mvfderiv
  · have hn : ¬ DifferentiableAt ℝ (f ∘ (extChartAt I x).symm)
        (extChartAt I x x) := by
      intro hd
      apply hf
      rw [← mdifferentiableWithinAt_univ]
      apply DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm
      simpa [I.range_eq_univ] using hd.differentiableWithinAt
    rw [fderiv_zero_of_not_differentiableAt hn]
    simp [mvfderiv, mfderiv, hf]

omit [CompleteSpace E] in
private lemma directionalDerivative_in_chart
    (f : M → ℂ) (hf : MDifferentiable I 𝓘(ℝ, ℂ) f)
    (Y : (p : M) → TangentSpace I p) (x : M) :
    ((fun p => mvfderiv I f p (Y p)) ∘ (extChartAt I x).symm)
      =ᶠ[𝓝 (extChartAt I x x)]
        (fun y => fderiv ℝ (f ∘ (extChartAt I x).symm) y
          (VectorField.mpullbackWithin 𝓘(ℝ, E) I
            (extChartAt I x).symm Y (range I) y)) := by
  filter_upwards [extChartAt_target_mem_nhds (I := I) x] with y hy
  have hd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm y := by
    rw [← mdifferentiableWithinAt_univ]
    simpa [I.range_eq_univ] using mdifferentiableWithinAt_extChartAt_symm hy
  have hi : (mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm y).IsInvertible := by
    simpa [I.range_eq_univ] using isInvertible_mfderivWithin_extChartAt_symm hy
  have hc := mvfderiv_comp y (hf ((extChartAt I x).symm y)) hd
  rw [mvfderiv_eq_fderiv] at hc
  simp only [comp_apply, VectorField.mpullbackWithin_apply,
    I.range_eq_univ, mfderivWithin_univ]
  rw [hc, ContinuousLinearMap.comp_apply]
  congr 1
  exact (hi.self_apply_inverse (Y ((extChartAt I x).symm y))).symm

/-- The actual manifold bracket acts on smooth scalar functions by the
commutator of directional derivatives. -/
theorem smoothVectorFieldCommutator_proof :
    smoothVectorFieldCommutator I M := by
  intro V W hV hW f hf x
  let φ := extChartAt I x
  let z := φ x
  let V' : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm V (range I)
  let W' : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm W (range I)
  have hφ : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm z := by
    rw [← contMDiffWithinAt_univ]
    simpa only [I.range_eq_univ] using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x
  have hf' : ContDiffAt ℝ ∞ (f ∘ φ.symm) z :=
    ((hf (φ.symm z)).comp z hφ).contDiffAt
  have hV' : DifferentiableAt ℝ V' z := by
    simpa only [V', φ, z, preimage_univ, univ_inter, I.range_eq_univ,
      differentiableWithinAt_univ] using
      (hV x).mdifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
        (s := univ)
  have hW' : DifferentiableAt ℝ W' z := by
    simpa only [W', φ, z, preimage_univ, univ_inter, I.range_eq_univ,
      differentiableWithinAt_univ] using
      (hW x).mdifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
        (s := univ)
  have hbase (Y : (p : M) → TangentSpace I p) :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm Y (range I) z = Y x := by
    simp only [VectorField.mpullbackWithin_apply, φ, z,
      mfderivWithin_extChartAt_symm_inverse_apply]
    exact congrArg (fun p : M => (Y p : E)) (extChartAt_to_inv (I := I) x)
  have hb : VectorField.mlieBracket I V W x =
      VectorField.lieBracket ℝ V' W' z := by
    simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
      preimage_univ, univ_inter]
    change (mfderiv I 𝓘(ℝ, E) φ x).inverse
      (VectorField.lieBracketWithin (E := E) ℝ V' W' (range I) z) = _
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id]
    change VectorField.lieBracketWithin ℝ V' W' (range I) z =
      VectorField.lieBracket ℝ V' W' z
    rw [I.range_eq_univ, VectorField.lieBracketWithin_univ]
  have hcomm := VectorField.fderiv_apply_lieBracket hf' (by simp) hW' hV'
  rw [show V' z = V x from hbase V, show W' z = W x from hbase W] at hcomm
  rw [hb, scalarDerivative_in_chart f x,
    scalarDerivative_in_chart (fun y => mvfderiv I f y (W y)) x,
    scalarDerivative_in_chart (fun y => mvfderiv I f y (V y)) x,
    (directionalDerivative_in_chart f (hf.mdifferentiable (by simp)) W x).fderiv_eq,
    (directionalDerivative_in_chart f (hf.mdifferentiable (by simp)) V x).fderiv_eq]
  exact hcomm

end Langlands.Geometry.Manifold
