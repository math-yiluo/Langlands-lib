import Langlands.Automorphic.GroupSchemeUniformGrowthAutomorphicTaylor
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Mathlib.Analysis.Analytic.Order

/-! # Taylor coefficient pole detection on a complex line -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry Filter Set
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Analysis

/-- A scalar analytic germ `den` divides `num` at the point if their local
quotient can be represented by a function analytic at that point. -/
def AnalyticallyDividesAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (den num : E → ℂ) (z : E) : Prop :=
  ∃ b : E → ℂ, AnalyticAt ℂ b z ∧ num =ᶠ[𝓝 z] den * b

/-- Analytic divisibility on a complex line follows by factoring the common
power of the centered coordinate and dividing by a nonvanishing analytic germ. -/
theorem analyticallyDividesAt_of_order_le {den num : ℂ → ℂ} {z : ℂ}
    (hd : AnalyticAt ℂ den z) (hn : AnalyticAt ℂ num z)
    (hdne : analyticOrderAt den z ≠ ⊤)
    (hord : analyticOrderAt den z ≤ analyticOrderAt num z) :
    AnalyticallyDividesAt den num z := by
  let m := analyticOrderNatAt den z
  have hm : (m : ℕ∞) = analyticOrderAt den z := Nat.cast_analyticOrderNatAt hdne
  obtain ⟨u, hu, hune, hdeq⟩ := (hd.analyticOrderAt_eq_natCast).mp hm.symm
  obtain ⟨b, hb, hneq⟩ := (natCast_le_analyticOrderAt hn).mp (hm.trans_le hord)
  refine ⟨fun t => b t / u t, hb.div hu hune, ?_⟩
  filter_upwards [hdeq, hneq, hu.continuousAt.tendsto.eventually (eventually_ne_nhds hune)]
    with t hdt hnt hut
  simp only [Pi.mul_apply, hnt, hdt, smul_eq_mul, mul_assoc]
  rw [mul_comm (u t), div_mul_cancel₀ _ hut]

end Langlands.Analysis

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global Langlands.Analysis Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L

/-- Suppose scalar tests separate automorphic vectors. For a weakly holomorphic
curve in the growth stage with automorphic values on a nonempty open subset,
local divisibility of all test values by a given nonzero analytic germ implies
local divisibility of every continuous scalar evaluation by that germ. -/
theorem analyticallyDividesAt_of_automorphic_tests
    (K : Subgroup (InfiniteAdelicGroupPoints F G)) (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {U W : Set ℂ} (hU : IsPreconnected U) (hUo : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U)
    (hne : W.Nonempty) (f : ℂ → 𝔉)
    (hf : ∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (hform : ∀ t ∈ W, IsAutomorphicFunctionOn F G hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F G) K rho (value (f t)))
    {κ : Type*} (obs : κ → 𝔉 →L[ℂ] ℂ)
    (hdetect : ∀ v : 𝔉, IsAutomorphicFunctionOn F G hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F G) K rho (value v) → (∀ i, obs i v = 0) → v = 0)
    (z : U) (den : ℂ → ℂ) (hd : AnalyticAt ℂ den z.val)
    (hdne : analyticOrderAt den z.val ≠ ⊤)
    (hobs : ∀ i, AnalyticallyDividesAt den (fun t => obs i (f t)) z.val)
    (test : 𝔉 →L[ℂ] ℂ) : AnalyticallyDividesAt den (fun t => test (f t)) z.val := by
  let m := analyticOrderNatAt den z.val
  have hm : (m : ℕ∞) = analyticOrderAt den z.val := Nat.cast_analyticOrderNatAt hdne
  have han (φ : 𝔉 →L[ℂ] ℂ) : AnalyticAt ℂ (fun t => φ (f t)) z.val :=
    (hf φ).analyticOnNhd hUo _ z.property
  have hobsderiv (i : κ) : ∀ k < m, iteratedDeriv k (fun t => obs i (f t)) z.val = 0 := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han (obs i))).mp
    obtain ⟨b, hb, hbeq⟩ := hobs i
    rw [hm, analyticOrderAt_congr hbeq, analyticOrderAt_mul hd hb]
    exact le_add_of_nonneg_right zero_le
  apply analyticallyDividesAt_of_order_le hd (han test) hdne
  rw [← hm, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han test)]
  intro k hk
  let a := taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z
  have hform_a : IsAutomorphicFunctionOn F G hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F G) K rho (value a) :=
    (isAutomorphicFunctionOn_evaluate_iff F G hsmooth hcalc rho K
      (a : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).mpr
      (isAdelicAutomorphicForm_taylorCoefficient F G rho hsmooth hcalc hN hrho R L
        K hL hU hUo hW hWU hne f hf hform z k)
  have hzero : a = 0 := hdetect a hform_a fun i => by
    change obs i (taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z) = 0
    rw [apply_taylorCoefficient, hobsderiv i k hk, zero_div]
  have heval := apply_taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z test
  change test a = _ at heval
  rw [hzero, map_zero] at heval
  exact (div_eq_zero_iff.mp heval.symm).resolve_right
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
