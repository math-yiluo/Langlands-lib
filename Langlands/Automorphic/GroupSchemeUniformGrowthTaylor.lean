import Langlands.Automorphic.GroupSchemeUniformGrowthClosed
import Langlands.Automorphic.GroupSchemeUniformGrowthHolomorphy
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Taylor coefficients in the actual uniform moderate growth space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology Set
open scoped CategoryTheory.MonObj ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth
local notation "B" => lp (fun _ : AdelicGroupPoints F G => ℂ) ∞
local notation "T" => derivativeCoordinates F G rho hsmooth hcalc hN hrho R L
local notation "D" => weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L

/-- The product of weighted derivative maps induces the defining topology. -/
theorem isInducing_derivativeCoordinates : IsInducing T := by
  constructor
  change (⨅ a : UEA, TopologicalSpace.induced (D a) inferInstance) =
    TopologicalSpace.induced T
      (⨅ a : UEA, TopologicalSpace.induced (fun p : UEA → B => p a) inferInstance)
  simp only [induced_iInf, induced_compose]
  rfl

variable {U : Set ℂ}

private theorem exists_weakDerivative
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) (hU : IsOpen U) (f : ℂ → V)
    (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (f s)) U) (z : U) :
    ∃ v : V, ∀ test : V →L[ℂ] ℂ,
      HasDerivAt (fun s => test (f s)) (test v) z.val := by
  let q (w : ℂ) : V := (w - z.val)⁻¹ • (f w - f z.val)
  let v (a : UEA) : B := deriv (fun w => D a (f w)) z.val
  have hT : Tendsto (T ∘ q) (𝓝[≠] z.val) (𝓝 v) := by
    apply tendsto_pi_nhds.mpr
    intro a
    have ha := analyticOnNhd_weightedDerivative F G rho hsmooth hcalc hN hrho R L hU hf a
    have hd := ((ha z.val z.property).differentiableAt).hasDerivAt.tendsto_slope
    change Tendsto (fun w => D a (q w)) (𝓝[≠] z.val) (𝓝 (v a))
    rw [show (fun w => D a (q w)) = slope (fun w => D a (f w)) z.val from by
      funext w
      simp only [slope_def_module, q, map_smul, map_sub]]
    exact hd
  have hClosed := isClosed_range_derivativeCoordinates F G rho hsmooth hcalc hN hrho R L hL
  obtain ⟨g, hg⟩ := hClosed.mem_of_tendsto hT (Eventually.of_forall fun w => ⟨q w, rfl⟩)
  have hq : Tendsto q (𝓝[≠] z.val) (𝓝 g) := by
    apply (isInducing_derivativeCoordinates F G rho hsmooth hcalc hN hrho R L).tendsto_nhds_iff.mpr
    rwa [hg]
  refine ⟨g, fun test => hasDerivAt_iff_tendsto_slope.mpr ?_⟩
  rw [show slope (fun w => test (f w)) z.val = test ∘ q from by
    funext w
    simp only [slope_def_module, Function.comp_apply, q, map_sub, map_smul]]
  exact (test.continuous.tendsto g).comp hq

private theorem exists_iteratedWeakDerivative
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) (hU : IsOpen U) (f : ℂ → V)
    (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (f s)) U) (n : ℕ) :
    ∃ g : ℂ → V, ∀ (z : U) (test : V →L[ℂ] ℂ),
      test (g z.val) = iteratedDeriv n (fun t => test (f t)) z.val := by
  classical
  have han (test : V →L[ℂ] ℂ) (i : ℕ) :
      AnalyticOnNhd ℂ (iteratedDeriv i (fun t => test (f t))) U := by
    induction i with
    | zero => simpa only [iteratedDeriv_zero] using (hf test).analyticOnNhd hU
    | succ i hi => rw [iteratedDeriv_succ]; exact hi.deriv
  induction n with
  | zero => exact ⟨f, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih
    have hEg (test : V →L[ℂ] ℂ) :
        EqOn (fun t => test (g t)) (iteratedDeriv n (fun t => test (f t))) U :=
      fun _ hz => hg ⟨_, hz⟩ test
    have hdg (test : V →L[ℂ] ℂ) : DifferentiableOn ℂ (fun t => test (g t)) U :=
      (han test n).differentiableOn.congr (hEg test)
    let jet (z : U) := Classical.choose
      (exists_weakDerivative F G rho hsmooth hcalc hN hrho R L hL hU g hdg z)
    refine ⟨fun t => if ht : t ∈ U then jet ⟨t, ht⟩ else 0, fun z test => ?_⟩
    simp only [dite_eq_left z.property, iteratedDeriv_succ]
    have hd := Classical.choose_spec
      (exists_weakDerivative F G rho hsmooth hcalc hN hrho R L hL hU g hdg z) test
    have hEv : (fun t => test (g t)) =ᶠ[𝓝 z.val] iteratedDeriv n (fun t => test (f t)) := by
      filter_upwards [hU.mem_nhds z.property] with t ht using hEg test ht
    exact hd.deriv.symm.trans hEv.deriv_eq

/-- The factorial-normalized Taylor coefficient is an actual vector at the
same open finite level and uniform moderate growth exponent. -/
def taylorCoefficient
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) (hU : IsOpen U) (f : ℂ → V)
    (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (f s)) U) (n : ℕ) (z : U) : V :=
  (n.factorial : ℂ)⁻¹ • (Classical.choose
    (exists_iteratedWeakDerivative F G rho hsmooth hcalc hN hrho R L hL hU f hf n)) z.val

/-- Every continuous linear scalar test reads the corresponding scalar Taylor coefficient. -/
theorem apply_taylorCoefficient
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) (hU : IsOpen U) (f : ℂ → V)
    (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (f s)) U)
    (n : ℕ) (z : U) (test : V →L[ℂ] ℂ) :
    test (taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hU f hf n z) =
      iteratedDeriv n (fun t => test (f t)) z.val / (n.factorial : ℂ) := by
  rw [taylorCoefficient, map_smul]
  rw [Classical.choose_spec
    (exists_iteratedWeakDerivative F G rho hsmooth hcalc hN hrho R L hL hU f hf n) z test]
  rw [smul_eq_mul, div_eq_mul_inv, mul_comm]

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
