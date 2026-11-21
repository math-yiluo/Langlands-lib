import Langlands.Representation.Archimedean.OrthogonalGroupAveraging
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Finite rank of convolution by an orthogonal entry polynomial -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Langlands.Archimedean.OrthogonalFinitePolynomial

variable {n : ℕ}

local notation "K" => Matrix.unitaryGroup (Fin n) ℝ

local instance secondCountableTopology_orthogonal : SecondCountableTopology K := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology
    (Matrix.unitaryGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ))

private def rightTranslation (k : K) : C(K, ℂ) →L[ℂ] C(K, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ ⟨fun x => x * k, continuous_id.mul continuous_const⟩

private theorem continuous_rightTranslation :
    Continuous (fun p : K × C(K, ℂ) => rightTranslation p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (K × C(K, ℂ)) × K => p.1.2 (p.2 * p.1.1))
  have heval : Continuous (fun p : C(K, ℂ) × K => p.1 p.2) := continuous_eval
  exact heval.comp ((continuous_snd.comp continuous_fst).prodMk
    (continuous_snd.mul (continuous_fst.comp continuous_fst)))

/-- Compact right convolution by a continuous coefficient on the orthogonal group. -/
def convolution (μ : Measure K) [IsFiniteMeasure μ] (φ : C(K, ℂ)) :
    C(K, ℂ) →L[ℂ] C(K, ℂ) :=
  compactAverage μ (continuous_rightTranslation (n := n)) φ

variable (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)) [μ.IsHaarMeasure]

@[simp]
theorem convolution_apply (φ f : C(K, ℂ)) (x : K) :
    convolution μ φ f x = ∫ k, φ k * f (x * k) ∂μ := by
  have hC : Continuous (fun k : K => φ k • rightTranslation k f) :=
    φ.continuous.smul (continuous_rightTranslation.comp (continuous_id.prodMk continuous_const))
  have hI := integrable_of_continuous μ hC
  have h := ((ContinuousMap.evalCLM ℂ (M := ℂ) x).integral_comp_comm hI).symm
  change (ContinuousMap.evalCLM ℂ (M := ℂ) x) (∫ k, φ k • rightTranslation k f ∂μ) = _
  rw [h]
  rfl

private theorem continuous_of_mem_polynomialFunctions {h : K → ℂ}
    (hh : h ∈ polynomialFunctions n) : Continuous h := by
  obtain ⟨p, hp⟩ := exists_mvPolynomial_of_mem_polynomialFunctions hh
  have hc : Continuous (fun k : K => fun ij : Fin n × Fin n => entry n ij k) :=
    continuous_pi fun ij => (entry n ij).continuous
  have hEq : h = fun k => MvPolynomial.eval (fun ij => entry n ij k) p := funext hp
  rw [hEq]
  exact p.continuous_eval.comp hc

private theorem exists_finiteDimensional_integral_range
    {h : K → K → ℂ} (hh : h ∈ separated n) :
    (∀ x, Continuous (h x)) ∧
      ∃ W : Submodule ℂ C(K, ℂ), FiniteDimensional ℂ W ∧
        ∀ f : C(K, ℂ), ∃ g ∈ W, ∀ x, g x = ∫ k, h x k * f k ∂μ := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨α, hα, β, rfl⟩ := hh
    let a : C(K, ℂ) := ⟨α, continuous_of_mem_polynomialFunctions hα⟩
    let W := Submodule.span ℂ {a}
    refine ⟨fun x => continuous_const.mul β.continuous, W, inferInstance, ?_⟩
    intro f
    let c := ∫ k, β k * f k ∂μ
    refine ⟨c • a, W.smul_mem c (Submodule.subset_span rfl), fun x => ?_⟩
    change c * α x = ∫ k, α x * β k * f k ∂μ
    rw [mul_comm, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun k => (mul_assoc _ _ _).symm)
  | zero =>
    refine ⟨fun x => continuous_const, ⊥, inferInstance, fun f => ⟨0, zero_mem _, ?_⟩⟩
    intro x
    simp
  | add h h' _ _ ih ih' =>
    obtain ⟨hc, W, hW, hG⟩ := ih
    obtain ⟨hc', W', hW', hG'⟩ := ih'
    refine ⟨fun x => (hc x).add (hc' x), W ⊔ W', inferInstance, ?_⟩
    intro f
    obtain ⟨g, hg, he⟩ := hG f
    obtain ⟨g', hg', he'⟩ := hG' f
    refine ⟨g + g', Submodule.add_mem_sup hg hg', fun x => ?_⟩
    rw [ContinuousMap.add_apply, he x, he' x]
    have hi : Integrable (fun k => h x k * f k) μ :=
      integrable_of_continuous μ ((hc x).mul f.continuous)
    have hi' : Integrable (fun k => h' x k * f k) μ :=
      integrable_of_continuous μ ((hc' x).mul f.continuous)
    rw [← integral_add hi hi']
    exact integral_congr_ae (Eventually.of_forall fun k => (add_mul _ _ _).symm)
  | smul c h _ ih =>
    obtain ⟨hc, W, hW, hG⟩ := ih
    refine ⟨fun x => (hc x).const_smul c, W, hW, ?_⟩
    intro f
    obtain ⟨g, hg, he⟩ := hG f
    refine ⟨c • g, W.smul_mem c hg, fun x => ?_⟩
    simp only [ContinuousMap.smul_apply, he, smul_eq_mul, Pi.smul_apply, mul_assoc]
    exact (integral_const_mul _ _).symm

/-- For each polynomial weight, one finite-dimensional space contains every convolution
output, independently of the input function. -/
theorem finiteDimensional_convolution_range {φ : C(K, ℂ)} (hφ : φ ∈ polynomialStar n) :
    FiniteDimensional ℂ (LinearMap.range (convolution μ φ).toLinearMap) := by
  have hsub : φ ∈ (polynomialStar n).toSubalgebra := hφ
  rw [polynomialStar_toSubalgebra] at hsub
  obtain ⟨-, W, hW, hG⟩ := exists_finiteDimensional_integral_range μ (inv_mul_mem_separated hsub)
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  rintro _ ⟨f, rfl⟩
  obtain ⟨g, hg, he⟩ := hG f
  have hEq : convolution μ φ f = g := by
    apply ContinuousMap.ext
    intro x
    rw [convolution_apply, he x, ← integral_mul_left_eq_self (fun k => φ (x⁻¹ * k) * f k) x]
    simp only [inv_mul_cancel_left]
  change convolution μ φ f ∈ W
  rw [hEq]
  exact hg

end Langlands.Archimedean.OrthogonalFinitePolynomial
