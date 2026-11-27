import Langlands.Geometry.Manifold.LieGroupEllipticL2

/-! # Local Haar `L²` control of word derivatives for an elliptic word equation -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

set_option autoImplicit false

namespace Langlands.Geometry.Manifold

open Langlands.Analysis

section Words

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] [ChartedSpace E H] [Group H]

/-- A word in finitely many directions acts as the iterated directional derivative along the
list of its directions. -/
theorem lieWordDerivative_ofList_eq_foldr {m : ℕ} (Y : Fin m → GroupLieAlgebra 𝓘(ℝ, E) H)
    (w : List (Fin m)) (φ : H → ℂ) :
    (lieWordDerivative Y (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ =
      (w.map Y).foldr (groupDirectionalValue 𝓘(ℝ, E)) φ := by
  induction w with
  | nil => exact lieWordDerivative_ofList_nil Y φ
  | cons i w ih =>
    rw [lieWordDerivative_ofList_cons, ih]
    rfl

/-- Every list of directions is a word in the directions it enumerates. -/
theorem foldr_groupDirectionalValue_eq_lieWordDerivative (D : List (GroupLieAlgebra 𝓘(ℝ, E) H))
    (φ : H → ℂ) :
    D.foldr (groupDirectionalValue 𝓘(ℝ, E)) φ =
      (lieWordDerivative (fun i : Fin D.length => D.get i)
        (FreeMonoid.ofList (List.finRange D.length)) : (H → ℂ) → H → ℂ) φ := by
  rw [lieWordDerivative_ofList_eq_foldr, List.map_get_finRange]

end Words

/-- **Word derivatives of solutions of an elliptic word equation.** For one positive-order
elliptic left-invariant word operator and every word `w` in arbitrary tangent directions `Y`,
the value at the identity of the `w`-derivative of every smooth solution is bounded by its Haar
`L²` norm on a fixed compact set, with a constant independent of the solution. -/
theorem exists_lieWord_derivative_l2_evaluation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [Group H] [TopologicalSpace H]
    [ChartedSpace E H] [LieGroup 𝓘(ℝ, E) ∞ H] [IsTopologicalGroup H] [SecondCountableTopology H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]
    {n r : ℕ} (hr : 0 < r) (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (Ptop Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (htop : ∀ w ∈ Ptop.coeff.support, w.length = r)
    (hlow : ∀ w ∈ Plow.coeff.support, w.length < r)
    (hell : ∀ ξ : GroupLieAlgebra 𝓘(ℝ, E) H →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0)
    {m : ℕ} (Y : Fin m → GroupLieAlgebra 𝓘(ℝ, E) H) (w : List (Fin m)) :
    ∃ (V : Set H) (C : ℝ≥0∞), IsCompact V ∧ C ≠ ⊤ ∧
      ∀ φ : H → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ →
        (∀ x, lieWordAction X (Ptop + Plow) φ x = 0) →
        ‖(lieWordDerivative Y (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ 1‖ₑ ≤
          C * eLpNorm φ 2 (μ.restrict V) := by
  classical
  let d := Module.finrank ℝ E
  let F := EuclideanSpace ℝ (Fin d)
  let L : E ≃L[ℝ] F := toEuclidean
  let e := extChartAt 𝓘(ℝ, E) (1 : H)
  let S := L.symm ⁻¹' e.target
  let ψ := e.symm ∘ L.symm
  let x₀ := L (e 1)
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  obtain ⟨D, _, _, _, hψ₀, hψ, hD, hcoef, hellD, haction, _⟩ :=
    exists_lieWordCoordinateOperator X Ptop Plow htop hlow hell
  obtain ⟨S', ψ', x₀', V', hS', hx₀', _, hψ', hSeq, hψeq, hx₀eq, hV', _, hdir'⟩ :=
    exists_lieGroupChartFrame_extChart Y
  subst hSeq hψeq hx₀eq
  obtain ⟨R, hR, hRS, c, hc, hdom⟩ := exists_chartVolume_le_smul_haar (E := E) μ
  have hballS : ball x₀ R ⊆ S := ball_subset_closedBall.trans hRS
  obtain ⟨ρ, _, hρR, C, hC, hest⟩ := exists_localElliptic_interior_derivative_l2_bounds
    hr D hD isOpen_ball (fun k W => (hcoef k W).mono hballS) (mem_ball_self hR) hellD
  let V := ψ '' closedBall x₀ R
  have hV : IsCompact V :=
    (isCompact_closedBall _ _).image_of_continuousOn (hψ.continuousOn.mono hRS)
  let ν := (volume : Measure F).restrict (closedBall x₀ R)
  have hψm : AEMeasurable ψ ν :=
    (hψ.continuousOn.mono hRS).aemeasurable measurableSet_closedBall
  have hνV : (ν.map ψ).restrict V = ν.map ψ := by
    apply Measure.restrict_eq_self_of_ae_mem
    refine (ae_map_iff hψm hV.measurableSet).mpr ?_
    exact ae_restrict_of_forall_mem measurableSet_closedBall fun x hx => mem_image_of_mem ψ hx
  have hbound : ν.map ψ ≤ c • μ.restrict V := by
    rw [← Measure.restrict_smul, ← hνV]
    exact Measure.restrict_mono_measure hdom V
  -- the constant: coefficients of the word at the chart point times the interior constants
  let N := w.length
  let A : ℝ≥0∞ := ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
    ‖vectorFieldWordCoeff V' w k W x₀‖ₑ * C k
  have hA : A ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun W _ => ?_
    exact ENNReal.mul_ne_top enorm_ne_top (hC k)
  refine ⟨V, A * c ^ (1 / 2 : ℝ), hV,
    ENNReal.mul_ne_top hA (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc), ?_⟩
  intro φ hφ hsol
  have hφψ := contMDiffOn_iff_contDiffOn.mp (hφ.comp_contMDiffOn hψ)
  have hφD (x : F) (hx : x ∈ ball x₀ R) : D.action (φ ∘ ψ) x = 0 :=
    (haction φ hφ x (hballS hx)).trans (hsol (ψ x))
  -- the `L²` norm on the small ball is controlled by the Haar norm on `V`
  have hLp : eLpNorm (φ ∘ ψ) 2 (volume.restrict (closedBall x₀ ρ)) ≤ eLpNorm φ 2 (ν.map ψ) := by
    rw [eLpNorm_map_measure hφ.continuous.aestronglyMeasurable hψm]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ (hρR.trans ball_subset_closedBall))
  have hLp' := eLpNorm_le_of_measure_le_smul hbound (f := φ) (p := 2)
  have hhalf : (1 / (2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hhalf, smul_eq_mul] at hLp'
  set Q := eLpNorm (φ ∘ ψ) 2 (volume.restrict (closedBall x₀ ρ)) with hQ
  -- the chart expansion of the word derivative at the identity
  have hexp := lieWordDerivative_chart_expansion Y hS' hψ' hV' hdir' hφ w N le_rfl x₀ hx₀'
  change ψ x₀ = 1 at hψ₀
  have hexp' : (lieWordDerivative Y (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ 1 =
      ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
        vectorFieldWordCoeff V' w k W x₀ *
          iteratedFDeriv ℝ k (φ ∘ ψ) x₀ (fun q => b (W q)) := by
    rw [← hψ₀]
    exact hexp
  have hterm (k : ℕ) (W : Fin k → Fin d) :
      ‖vectorFieldWordCoeff V' w k W x₀ *
          iteratedFDeriv ℝ k (φ ∘ ψ) x₀ (fun q => b (W q))‖ₑ ≤
        ‖vectorFieldWordCoeff V' w k W x₀‖ₑ * C k * Q := by
    rw [enorm_mul, mul_assoc]
    refine mul_le_mul_right ?_ _
    have hmult : ‖iteratedFDeriv ℝ k (φ ∘ ψ) x₀ (fun q => b (W q))‖ ≤
        ‖iteratedFDeriv ℝ k (φ ∘ ψ) x₀‖ := by
      have h := (iteratedFDeriv ℝ k (φ ∘ ψ) x₀).le_opNorm (fun q => b (W q))
      have hprod : ∏ q, ‖b (W q)‖ = 1 :=
        Finset.prod_eq_one fun q _ => b.orthonormal.1 (W q)
      rwa [hprod, mul_one] at h
    calc ‖iteratedFDeriv ℝ k (φ ∘ ψ) x₀ (fun q => b (W q))‖ₑ
        ≤ ‖iteratedFDeriv ℝ k (φ ∘ ψ) x₀‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hmult
      _ ≤ C k * Q := hest (φ ∘ ψ) (hφψ.mono hballS) hφD k
  calc ‖(lieWordDerivative Y (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ 1‖ₑ
      = ‖∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
          vectorFieldWordCoeff V' w k W x₀ *
            iteratedFDeriv ℝ k (φ ∘ ψ) x₀ (fun q => b (W q))‖ₑ := by rw [hexp']
    _ ≤ ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
          ‖vectorFieldWordCoeff V' w k W x₀‖ₑ * C k * Q := by
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun W _ => hterm k W)
    _ = A * Q := by
        simp only [A, Finset.sum_mul]
    _ ≤ A * (c ^ (1 / 2 : ℝ) * eLpNorm φ 2 (μ.restrict V)) :=
        mul_le_mul_right (hLp.trans hLp') _
    _ = A * c ^ (1 / 2 : ℝ) * eLpNorm φ 2 (μ.restrict V) := by rw [mul_assoc]

end Langlands.Geometry.Manifold
