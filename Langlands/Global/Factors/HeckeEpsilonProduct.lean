import Langlands.Global.Factors.HeckeConductorSupport
import Langlands.LocalFactor.Abelian.GaussDual

/-! # The actual finite epsilon product as an entire nonvanishing function -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField Langlands.HarmonicAnalysis
open Langlands.LocalFactor.PadicAbelian

variable {K : Type u} [Field K] [NumberField K]

variable (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (μ : ∀ v : FinitePlace K,
      SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))

/-- The logarithmic spectral slope of the actual local epsilon expression. -/
def finiteEpsilonLogSlope (v : FinitePlace K) : ℂ :=
  -(((CompletionPadic.topologicalData v).additiveConductor (ψf v) +
      ((CompletionPadic.topologicalData v).multiplicativeConductor
        (χ.finiteComponent v) : ℤ) : ℤ) : ℂ) *
    (Real.log ((CompletionPadic.topologicalData v).residueCardinality : ℝ) : ℂ)

/-- The actual unordered finite-place epsilon product. -/
def finiteGlobalEpsilon (s : ℂ) : ℂ :=
  ∏' v : FinitePlace K, finiteEpsilon χ ψf μ v s

/-- Every supplied local self-dual Haar measure gives a nonzero local epsilon. -/
theorem finiteEpsilon_ne_zero (v : FinitePlace K) (s : ℂ) :
    finiteEpsilon χ ψf μ v s ≠ 0 := by
  let T := CompletionPadic.topologicalData v
  let := T.topology
  let : MeasurableSpace (CompletionPadic.padicField v).Carrier := borel _
  exact epsilonAt_ne_zero T (uniformizerUnit T) (χ.finiteComponent v)
    ((conductorAt_iff T (χ.finiteComponent v) _).mpr rfl)
    (ψf v) (T.additiveConductor (ψf v)) (μ v).val
    ((additiveConductorAt_iff T (ψf v) _).mpr rfl) s

/-- The exact spectral dependence of each actual finite epsilon factor. -/
theorem finiteEpsilon_eq_zero_mul_exp (v : FinitePlace K) (s : ℂ) :
    finiteEpsilon χ ψf μ v s = finiteEpsilon χ ψf μ v 0 *
      Complex.exp (finiteEpsilonLogSlope χ ψf v * s) := by
  let T := CompletionPadic.topologicalData v
  let := T.topology
  let : MeasurableSpace (CompletionPadic.padicField v).Carrier := borel _
  have h : finiteEpsilon χ ψf μ v s = finiteEpsilon χ ψf μ v 0 *
      Complex.exp (-((T.additiveConductor (ψf v) +
        (T.multiplicativeConductor (χ.finiteComponent v) : ℤ) : ℤ) : ℂ) *
          s * (Real.log (T.residueCardinality : ℝ) : ℂ)) :=
    epsilonAt_eq_zero_mul T (uniformizerUnit T) (χ.finiteComponent v) (ψf v).toAddChar
      (μ v).val.measure (T.multiplicativeConductor (χ.finiteComponent v))
      (T.additiveConductor (ψf v)) s
  refine h.trans ?_
  congr 2
  unfold finiteEpsilonLogSlope
  dsimp [T]
  ring

/-- Each actual local epsilon is entire in the spectral parameter. -/
theorem finiteEpsilon_differentiable (v : FinitePlace K) :
    Differentiable ℂ (finiteEpsilon χ ψf μ v) := by
  let T := CompletionPadic.topologicalData v
  let := T.topology
  let : MeasurableSpace (CompletionPadic.padicField v).Carrier := borel _
  exact epsilonAt_differentiable T (uniformizerUnit T) (χ.finiteComponent v)
    (ψf v).toAddChar (μ v).val.measure
    (T.multiplicativeConductor (χ.finiteComponent v)) (T.additiveConductor (ψf v))

/-- Any finite exceptional set valid at all parameters computes the same product. -/
theorem finiteGlobalEpsilon_eq_prod (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, ∀ s : ℂ, finiteEpsilon χ ψf μ v s = 1) (s : ℂ) :
    finiteGlobalEpsilon χ ψf μ s = ∏ v ∈ S, finiteEpsilon χ ψf μ v s := by
  exact tprod_eq_prod (fun v hv => hS v hv s)

/-- The finite exceptional product has its exact exponential spectral law. -/
theorem prod_finiteEpsilon_eq_zero_mul_exp (S : Finset (FinitePlace K)) (s : ℂ) :
    (∏ v ∈ S, finiteEpsilon χ ψf μ v s) =
      (∏ v ∈ S, finiteEpsilon χ ψf μ v 0) *
        Complex.exp ((∑ v ∈ S, finiteEpsilonLogSlope χ ψf v) * s) := by
  calc
    (∏ v ∈ S, finiteEpsilon χ ψf μ v s) =
        ∏ v ∈ S, finiteEpsilon χ ψf μ v 0 *
          Complex.exp (finiteEpsilonLogSlope χ ψf v * s) :=
      Finset.prod_congr rfl (fun v _ => finiteEpsilon_eq_zero_mul_exp χ ψf μ v s)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.sum_mul, Complex.exp_sum]

section ActualGlobalData

variable (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ x : K, ψ (diagonal K x) = 1)
    (hf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (hR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (hC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v))

include ψ hdiag hf aR hR aC hC

/-- The unordered product converges for every parameter, using actual global data. -/
theorem finiteGlobalEpsilon_hasProd (s : ℂ) :
    HasProd (fun v => finiteEpsilon χ ψf μ v s) (finiteGlobalEpsilon χ ψf μ s) := by
  obtain ⟨S, hS⟩ := exists_finset_finiteEpsilon_eq_one ψ hdiag ψf hf aR hR aC hC χ μ
  rw [finiteGlobalEpsilon_eq_prod χ ψf μ S hS s]
  exact hasProd_prod_of_ne_finset_one (fun v hv => hS v hv s)

/-- The actual finite epsilon product is entire. -/
theorem finiteGlobalEpsilon_differentiable :
    Differentiable ℂ (finiteGlobalEpsilon χ ψf μ) := by
  obtain ⟨S, hS⟩ := exists_finset_finiteEpsilon_eq_one ψ hdiag ψf hf aR hR aC hC χ μ
  have he : finiteGlobalEpsilon χ ψf μ =
      fun s => ∏ v ∈ S, finiteEpsilon χ ψf μ v s :=
    funext (finiteGlobalEpsilon_eq_prod χ ψf μ S hS)
  rw [he]
  exact Differentiable.fun_finsetProd (fun v _ => finiteEpsilon_differentiable χ ψf μ v)

/-- No supplied self-dual local Haar measures produce a zero of the product. -/
theorem finiteGlobalEpsilon_ne_zero (s : ℂ) :
    finiteGlobalEpsilon χ ψf μ s ≠ 0 := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_finiteEpsilon_eq_one ψ hdiag ψf hf aR hR aC hC χ μ
  rw [finiteGlobalEpsilon_eq_prod χ ψf μ S hS s]
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => finiteEpsilon_ne_zero χ ψf μ v s)

/-- The reciprocal of the actual product is entire as well. -/
theorem finiteGlobalEpsilon_inv_differentiable :
    Differentiable ℂ (fun s => (finiteGlobalEpsilon χ ψf μ s)⁻¹) :=
  (finiteGlobalEpsilon_differentiable χ ψf μ ψ hdiag hf aR hR aC hC).inv
    (finiteGlobalEpsilon_ne_zero χ ψf μ ψ hdiag hf aR hR aC hC)

/-- The actual finite product has no meromorphic singularities. -/
theorem finiteGlobalEpsilon_meromorphic :
    MeromorphicOn (finiteGlobalEpsilon χ ψf μ) Set.univ := by
  intro s _
  exact ((finiteGlobalEpsilon_differentiable χ ψf μ ψ hdiag hf aR hR aC hC).analyticAt
    s).meromorphicAt

/-- A single finite sum of actual conductor slopes controls every parameter. -/
theorem exists_finiteGlobalEpsilon_spectral :
    ∃ A : ℂ, ∀ s : ℂ, finiteGlobalEpsilon χ ψf μ s =
      finiteGlobalEpsilon χ ψf μ 0 * Complex.exp (A * s) := by
  obtain ⟨S, hS⟩ := exists_finset_finiteEpsilon_eq_one ψ hdiag ψf hf aR hR aC hC χ μ
  refine ⟨∑ v ∈ S, finiteEpsilonLogSlope χ ψf v, fun s => ?_⟩
  rw [finiteGlobalEpsilon_eq_prod χ ψf μ S hS s,
    finiteGlobalEpsilon_eq_prod χ ψf μ S hS 0]
  exact prod_finiteEpsilon_eq_zero_mul_exp χ ψf μ S s

end ActualGlobalData

end Langlands.Global.HeckeFunctionalEquation
