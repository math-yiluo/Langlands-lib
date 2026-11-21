import Langlands.Global.RankinSelberg.ComplexLocalIntertwinerAnalytic
import Langlands.Global.RankinSelberg.ComplexMatrixConnected
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Evaluation at the identity determines a complex Whittaker intertwiner -/

noncomputable section

open Filter
open scoped ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Archimedean.ComplexLocalCasimir
open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "R" => rightDerivative (matrixModel ℂ n)
local notation "expM" => (NormedSpace.exp : M → M)

private def expCurve (X : M) (W : G → ℂ) (t : ℝ) : ℂ :=
  unitsExtension W (expM (t • X))

private theorem deriv_expCurve {W : G → ℂ}
    (hW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W) (X : M) :
    deriv (expCurve X W) = expCurve X (R X W) := by
  funext t
  let g : G := (NormedSpace.isUnit_exp (t • X)).unit
  have hg : g.val = expM (t • X) := IsUnit.unit_spec _
  have hder : HasDerivAt (fun u : ℝ => expM (u • X)) (g.val * X) t := by
    rw [hg]
    exact hasDerivAt_exp_smul_const X t
  have hd := ((differentiableAt_unitsExtension hW g.isUnit).hasFDerivAt.comp_hasDerivAt t hder).deriv
  change deriv (expCurve X W) t = fderiv ℝ (unitsExtension W) g.val (g.val * X) at hd
  rw [hd, ← rightDerivative_eq_fderiv hW X g, expCurve, ← hg, unitsExtension_val]

private theorem analyticOnNhd_expCurve {W : G → ℂ}
    (hW : AnalyticOnNhd ℝ (unitsExtension W) {h : M | IsUnit h}) (X : M) :
    AnalyticOnNhd ℝ (expCurve X W) Set.univ := by
  intro t _
  let L : ℝ →L[ℝ] M := (1 : ℝ →L[ℝ] ℝ).smulRight X
  have hExp : AnalyticAt ℝ expM (L t) :=
    NormedSpace.analyticAt_exp_of_mem_ball (L t)
      (by rw [NormedSpace.expSeries_radius_eq_top]; exact Metric.mem_eball.mpr (edist_lt_top _ _))
  have hAt := hW (expM (L t)) (NormedSpace.isUnit_exp (L t))
  have hL : AnalyticAt ℝ (fun u : ℝ => expM (u • X)) t := hExp.comp (L.analyticAt t)
  exact hAt.fun_comp (f := fun u : ℝ => expM (u • X)) hL

private theorem eventuallyEq_of_iteratedDeriv_eq {F F' : ℝ → ℂ}
    (hF : AnalyticAt ℝ F 0) (hF' : AnalyticAt ℝ F' 0)
    (h : ∀ k, iteratedDeriv k F 0 = iteratedDeriv k F' 0) : F =ᶠ[𝓝 0] F' := by
  obtain ⟨p, r, hp⟩ := hF
  obtain ⟨q, r', hq⟩ := hF'
  filter_upwards [Metric.eball_mem_nhds (0 : ℝ) hp.r_pos,
    Metric.eball_mem_nhds (0 : ℝ) hq.r_pos] with t ht ht'
  have h₁ := hp.hasSum_iteratedFDeriv ht
  have h₂ := hq.hasSum_iteratedFDeriv ht'
  simp only [zero_add, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, h] at h₁
  simp only [zero_add, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h₂
  exact h₁.unique h₂

private theorem map_exp_nhds_zero : Filter.map expM (𝓝 0) = 𝓝 (1 : M) := by
  have hExp : HasStrictFDerivAt expM ((ContinuousLinearEquiv.refl ℝ M) : M →L[ℝ] M) 0 :=
    hasStrictFDerivAt_exp_zero
  simpa only [NormedSpace.exp_zero] using hExp.map_nhds_eq_of_equiv

/-- Two real-analytic coefficient families with the same right derivative action
on the indexing type agree if their evaluations at the identity agree. -/
theorem eq_of_eval_one_of_analytic_rightDerivative {V : Type*} {A A' : V → G → ℂ}
    (D : M → V → V)
    (hA : ∀ v, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (A v))
    (hA' : ∀ v, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (A' v))
    (ha : ∀ v, AnalyticOnNhd ℝ (unitsExtension (A v)) {h : M | IsUnit h})
    (ha' : ∀ v, AnalyticOnNhd ℝ (unitsExtension (A' v)) {h : M | IsUnit h})
    (hD : ∀ X v, A (D X v) = R X (A v)) (hD' : ∀ X v, A' (D X v) = R X (A' v))
    (h₁ : ∀ v, A v 1 = A' v 1) : A = A' := by
  have hjet (X : M) (k : ℕ) (v : V) :
      iteratedDeriv k (expCurve X (A v)) 0 = iteratedDeriv k (expCurve X (A' v)) 0 := by
    induction k generalizing v with
    | zero =>
      simp only [iteratedDeriv_zero, expCurve, zero_smul, NormedSpace.exp_zero]
      change unitsExtension (A v) ((1 : G).val) = unitsExtension (A' v) ((1 : G).val)
      simpa only [unitsExtension_val] using h₁ v
    | succ k ih =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_expCurve (hA v),
        deriv_expCurve (hA' v), ← hD, ← hD']
      exact ih (D X v)
  have he (X : M) (v : V) : unitsExtension (A v) (expM X) =
      unitsExtension (A' v) (expM X) := by
    have hAx := analyticOnNhd_expCurve (ha v) X
    have hAx' := analyticOnNhd_expCurve (ha' v) X
    have hloc := eventuallyEq_of_iteratedDeriv_eq (hAx 0 (Set.mem_univ 0))
      (hAx' 0 (Set.mem_univ 0)) (fun k => hjet X k v)
    have heq := hAx.eqOn_of_preconnected_of_eventuallyEq hAx' isPreconnected_univ
      (Set.mem_univ (0 : ℝ)) hloc (Set.mem_univ (1 : ℝ))
    simpa only [expCurve, one_smul] using heq
  funext v g
  have hloc : unitsExtension (A v) =ᶠ[𝓝 (1 : M)] unitsExtension (A' v) := by
    rw [← map_exp_nhds_zero]
    change ∀ᶠ X in 𝓝 (0 : M), unitsExtension (A v) (expM X) = unitsExtension (A' v) (expM X)
    exact Filter.Eventually.of_forall fun X => he X v
  have heq := (ha v).eqOn_of_preconnected_of_eventuallyEq (ha' v)
    (isPreconnected_complexMatrixUnits n) (isUnit_one : IsUnit (1 : M)) hloc g.isUnit
  simpa only [unitsExtension_val] using heq

/-- A complex Whittaker intertwiner is determined by evaluation at `1`
on every vector of its compact-finite standard module. -/
theorem complexWhittakerIntertwiner_eq_of_eval_one {r : ℕ} {ds : List ComplexCharacterData}
    {a : ℂˣ}
    {B B' : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B)
    (hB' : IsComplexWhittakerIntertwiner r ds a B')
    (h₁ : ∀ f, B f 1 = B' f 1) : B = B' := by
  let D := fun X => envelopingAction (complexStandardLie (r + 1) ds) (realGenerator (r + 1) X)
  apply LinearMap.ext
  exact congrFun (eq_of_eval_one_of_analytic_rightDerivative (fun X v => D X v)
    hB.2.1 hB'.2.1 (analyticOnNhd_unitsExtension_complexWhittaker hB)
    (analyticOnNhd_unitsExtension_complexWhittaker hB')
    (fun X v => hB.2.2.2.2 X v _ (realGenerator_action ds X v))
    (fun X v => hB'.2.2.2.2 X v _ (realGenerator_action ds X v)) h₁)

/-- Distinct intertwiners on the same complex standard module cannot have the same
identity evaluations on every vector. -/
def ComplexLocalIntertwinerEvaluationStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B B' : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)),
    IsComplexWhittakerIntertwiner r ds a B → IsComplexWhittakerIntertwiner r ds a B' →
    (∀ f, B f 1 = B' f 1) → B = B'

theorem complexLocalIntertwinerEvaluation : ComplexLocalIntertwinerEvaluationStatement :=
  fun _ _ _ _ _ => complexWhittakerIntertwiner_eq_of_eval_one

end Langlands.Global.RankinSelbergGlobal
