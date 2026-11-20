import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Averaging continuous operator actions and testing with orthogonal polynomials -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Langlands.Archimedean

section Compact

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  (μ : Measure K) [IsFiniteMeasure μ] {A : K → E →L[ℂ] E}
  (hA : Continuous fun p : K × E => A p.1 p.2) (φ : C(K, ℂ))

private def averagedProfile (x : E) : C(K, E) :=
  ⟨fun k => φ k • A k x,
    φ.continuous.smul (hA.comp (continuous_id.prodMk continuous_const))⟩

omit [CompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
private theorem continuous_averagedProfile : Continuous (averagedProfile hA φ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : E × K => φ p.2 • A p.2 p.1)
  exact (φ.continuous.comp continuous_snd).smul (hA.comp (continuous_snd.prodMk continuous_fst))

omit [SecondCountableTopology K] in
include hA in
private theorem integrable_averagedProfile (x : E) : Integrable (fun k => φ k • A k x) μ :=
  (averagedProfile hA φ x).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Bochner averaging gives a bounded complex-linear operator on a complete space for
a jointly continuous operator family and a finite Borel measure on the compact parameter space. -/
def compactAverage [CompleteSpace E] : E →L[ℂ] E where
  toFun x := ∫ k, φ k • A k x ∂μ
  map_add' x y := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_averagedProfile μ hA φ x) (integrable_averagedProfile μ hA φ y)
  map_smul' z x := by
    simp only [map_smul, RingHom.id_apply]
    calc
      (∫ k, φ k • z • A k x ∂μ) = ∫ k, z • φ k • A k x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun k => smul_comm (φ k) z (A k x)
      _ = z • ∫ k, φ k • A k x ∂μ := integral_smul _ _
  cont := by
    let P := ContinuousMap.toLp (E := E) 1 μ ℂ
    have h : (fun x : E => ∫ k, φ k • A k x ∂μ) =
        (fun f : Lp E 1 μ => ∫ k, f k ∂μ) ∘ P ∘ averagedProfile hA φ := by
      funext x
      exact (integral_congr_ae (ContinuousMap.coeFn_toLp (E := E) (p := 1) (𝕜 := ℂ) μ
        (averagedProfile hA φ x))).symm
    rw [h]
    exact continuous_integral.comp (P.continuous.comp (continuous_averagedProfile hA φ))

@[simp]
theorem compactAverage_apply [CompleteSpace E] (x : E) :
    compactAverage μ hA φ x = ∫ k, φ k • A k x ∂μ := rfl

/-- Averages of orbits which lie in a closed submodule still lie in that submodule. -/
theorem compactAverage_mem [CompleteSpace E] [IsProbabilityMeasure μ]
    {W : Submodule ℂ E} (hW : IsClosed (W : Set E))
    {x : E} (hx : ∀ k, A k x ∈ W) : compactAverage μ hA φ x ∈ W := by
  rw [compactAverage_apply]
  exact (W.restrictScalars ℝ).convex.integral_mem hW
    (Eventually.of_forall fun k => W.smul_mem (φ k) (hx k)) (integrable_averagedProfile μ hA φ x)

end Compact

section Separation

variable {D : Type*} [AddCommGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D]
  [Module ℂ D] [Module ℝ D] [IsScalarTower ℝ ℂ D] [ContinuousSMul ℂ D]
  [LocallyConvexSpace ℝ D]

/-- A closed complex submodule can be separated from an exterior point by a continuous
complex-linear functional that vanishes on the submodule. -/
theorem exists_functional_vanishing_on_closedSubmodule {W : Submodule ℂ D}
    (hW : IsClosed (W : Set D)) {x : D} (hx : x ∉ W) :
    ∃ L : D →L[ℂ] ℂ, (∀ w ∈ W, L w = 0) ∧ L x ≠ 0 := by
  obtain ⟨L, c, hWc, hcx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (W.restrictScalars ℝ).convex hW hx
  have hc : 0 < c := by simpa using hWc 0 W.zero_mem
  refine ⟨L, ?_, fun h => (hc.trans (by simpa [h] using hcx)).false⟩
  intro w hw
  by_contra hn
  let z : ℂ := (c : ℂ) * (L w)⁻¹
  have he : L (z • w) = (c : ℂ) := by
    rw [map_smul, smul_eq_mul, show z * L w = (c : ℂ) by simp [z, hn]]
  have hl := hWc (z • w) (W.smul_mem z hw)
  rw [he] at hl
  change (c : ℂ).re < c at hl
  simp at hl

end Separation

open OrthogonalFinitePolynomial

/-- Polynomial-weighted integrals of a continuous orthogonal-group profile detect
whether all of its values belong to a given closed submodule. -/
theorem mem_closedSubmodule_of_polynomial_integrals_mem {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)) [μ.IsHaarMeasure]
    (f : C(Matrix.unitaryGroup (Fin n) ℝ, E)) {W : Submodule ℂ E} (hW : IsClosed (W : Set E))
    (h : ∀ φ ∈ polynomialStar n, (∫ k, φ k • f k ∂μ) ∈ W)
    (k : Matrix.unitaryGroup (Fin n) ℝ) : f k ∈ W := by
  by_contra hk
  obtain ⟨L, hL, hne⟩ := exists_functional_vanishing_on_closedSubmodule hW hk
  let g : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ) := ⟨fun x => L (f x), L.continuous.comp f.continuous⟩
  have hg : g = 0 := by
    apply eq_zero_of_integral_polynomial_mul_eq_zero μ g
    intro φ hφ
    have hInt : Integrable (fun x => φ x • f x) μ :=
      OrthogonalFinitePolynomial.integrable_of_continuous μ (φ.continuous.smul f.continuous)
    calc (∫ x, φ x * g x ∂μ) = L (∫ x, φ x • f x ∂μ) := by
          simpa only [g, ContinuousMap.coe_mk, map_smul, smul_eq_mul] using L.integral_comp_comm hInt
      _ = 0 := hL _ (h φ hφ)
  exact hne (ContinuousMap.congr_fun hg k)

end Langlands.Archimedean
