import Langlands.Global.AdelicTaylorPoleDetection
import Langlands.Analysis.SeveralComplex.HolomorphicSliceDivision

/-! # Removable singularities of quotients in the spaces of uniform moderate growth

Let `num` be a weakly holomorphic family in a space `𝔉^R_L` of uniform moderate growth and
`den` a scalar holomorphic function with nonzero germ at `s₀`. If every point evaluation of
`num` is `den` times a holomorphic scalar function `Φ(·)(g)`, then near `s₀` the functions
`Φ(s)` are the underlying functions of a weakly holomorphic `𝔉^R_L`-valued family. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Metric Set
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Analysis

/-- If `φ = t^k h` near `0` with `h` analytic at `0`, then the `k`-th derivative of `φ` at `0`
is `k! h(0)`. -/
theorem iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul {φ h : ℂ → ℂ} {k : ℕ}
    (hh : AnalyticAt ℂ h 0) (hφ : φ =ᶠ[𝓝 0] fun t => t ^ k * h t) :
    iteratedDeriv k φ 0 = k.factorial * h 0 := by
  rw [hφ.iteratedDeriv_eq k, iteratedDeriv_fun_mul (by fun_prop) hh.contDiffAt]
  rw [Finset.sum_eq_single k]
  · simp [Nat.descFactorial_self]
  · intro i hi hik
    have hki : k - i ≠ 0 := by
      have := Finset.mem_range.mp hi
      omega
    simp [hki]
  · intro hk
    exact absurd (Finset.self_mem_range_succ k) hk

/-- Let `ψ` have analytic order `k` at `0` and `φ = ψ χ` near `0`, with `χ` analytic at `0`.
Then the `k`-th derivatives at `0` satisfy `φ^{(k)}(0) = ψ^{(k)}(0) χ(0)`, and
`ψ^{(k)}(0) ≠ 0`. -/
theorem iteratedDeriv_eq_mul_of_analyticOrderAt_eq {φ ψ χ : ℂ → ℂ} {k : ℕ}
    (hψ : AnalyticAt ℂ ψ 0) (hχ : AnalyticAt ℂ χ 0) (hk : analyticOrderAt ψ 0 = k)
    (hφ : φ =ᶠ[𝓝 0] ψ * χ) :
    iteratedDeriv k φ 0 = iteratedDeriv k ψ 0 * χ 0 ∧ iteratedDeriv k ψ 0 ≠ 0 := by
  obtain ⟨g, hg, hg0, hψg⟩ := hψ.analyticOrderAt_eq_natCast.mp hk
  have h1 : iteratedDeriv k ψ 0 = k.factorial * g 0 :=
    iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul hg (by
      filter_upwards [hψg] with t ht
      rw [ht, sub_zero, smul_eq_mul])
  have h2 : iteratedDeriv k φ 0 = k.factorial * (g 0 * χ 0) :=
    iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul (hg.mul hχ) (by
      filter_upwards [hφ, hψg] with t ht ht'
      rw [ht, Pi.mul_apply, ht', sub_zero, smul_eq_mul, Pi.mul_apply, mul_assoc])
  refine ⟨by rw [h1, h2, mul_assoc], ?_⟩
  rw [h1]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) hg0

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

/-- On a complex line: if a scalar analytic germ `den` of finite order divides every point
evaluation of a weakly holomorphic curve in `𝔉^R_L`, then it divides every continuous scalar
evaluation of the curve. -/
theorem analyticallyDividesAt_of_eval
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {U : Set ℂ} (hUo : IsOpen U) (f : ℂ → 𝔉)
    (hf : ∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (z : U) (den : ℂ → ℂ) (hd : AnalyticAt ℂ den z.val)
    (hdne : analyticOrderAt den z.val ≠ ⊤)
    (hobs : ∀ y : AdelicGroupPoints F G,
      AnalyticallyDividesAt den (fun t => value (f t) y) z.val)
    (test : 𝔉 →L[ℂ] ℂ) : AnalyticallyDividesAt den (fun t => test (f t)) z.val := by
  let ev := UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho R L
  have hev (y : AdelicGroupPoints F G) (v : 𝔉) : ev y v = value v y :=
    UniformGrowthFrechetSpace.evalCLM_apply F G rho hsmooth hcalc hN hrho R L y v
  let m := analyticOrderNatAt den z.val
  have hm : (m : ℕ∞) = analyticOrderAt den z.val := Nat.cast_analyticOrderNatAt hdne
  have han (φ : 𝔉 →L[ℂ] ℂ) : AnalyticAt ℂ (fun t => φ (f t)) z.val :=
    (hf φ).analyticOnNhd hUo _ z.property
  have hobsderiv (y : AdelicGroupPoints F G) :
      ∀ k < m, iteratedDeriv k (fun t => ev y (f t)) z.val = 0 := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han (ev y))).mp
    obtain ⟨b, hb, hbeq⟩ := hobs y
    have hfun : (fun t => ev y (f t)) = fun t => value (f t) y := funext fun t => hev y (f t)
    rw [hfun, hm, analyticOrderAt_congr hbeq, analyticOrderAt_mul hd hb]
    exact le_add_of_nonneg_right zero_le
  apply analyticallyDividesAt_of_order_le hd (han test) hdne
  rw [← hm, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han test)]
  intro k hk
  let a := taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z
  have hzero : a = 0 := by
    apply toFun_injective F G rho hsmooth hcalc hN hrho R L
    funext y
    rw [← hev y a, ← hev y 0, map_zero]
    change ev y (taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z) = 0
    rw [apply_taylorCoefficient, hobsderiv y k hk, zero_div]
  have heval := apply_taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z test
  change test a = _ at heval
  rw [hzero, map_zero] at heval
  exact (div_eq_zero_iff.mp heval.symm).resolve_right
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Removable singularities in `𝔉^R_L`.** Let `num` be weakly holomorphic on an open `U`
with values in `𝔉^R_L`, `den` holomorphic on `U` with nonzero germ at `s₀ ∈ U`, and `Φ s` a
function on `G(𝔸)` for each `s`, holomorphic in `s ∈ U` at every point, such that
`num(s)(g) = den(s) Φ(s)(g)` on `U`. Then on a neighbourhood `V` of `s₀` the functions `Φ s`
are the underlying functions of a weakly holomorphic family `v : E → 𝔉^R_L`. -/
theorem exists_weaklyHolomorphic_of_mul_eq_eval
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {U : Set E} (hU : IsOpen U) {s₀ : E} (hs₀ : s₀ ∈ U)
    {num : E → 𝔉} {den : E → ℂ} {Φ : E → AdelicGroupPoints F G → ℂ}
    (hd : DifferentiableOn ℂ den U) (hdne : ¬ den =ᶠ[𝓝 s₀] 0)
    (hn : ∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (num s)) U)
    (hΦ : ∀ y, DifferentiableOn ℂ (fun s => Φ s y) U)
    (heq : ∀ s ∈ U, ∀ y, value (num s) y = den s * Φ s y) :
    ∃ V ⊆ U, IsOpen V ∧ s₀ ∈ V ∧ ∃ v : E → 𝔉,
      (∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (v s)) V) ∧
      ∀ s ∈ V, value (v s) = Φ s := by
  classical
  obtain ⟨u, r, V, hVo, hsV, hVU, hr, hr2, hline, hcircle⟩ :=
    exists_open_division_circle hU hs₀ hd hdne
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := mem_ball_self (by norm_num)
  have hsr : (r : ℂ) ∈ sphere (0 : ℂ) r := by simp [hr.le]
  have hbr : (r : ℂ) ∈ ball (0 : ℂ) 2 := mem_ball.mpr ((mem_sphere.mp hsr).trans_lt hr2)
  -- data on the slice through `s`
  have hlined (s : E) : Differentiable ℂ (fun t : ℂ => s + t • u) := by fun_prop
  have hnl (s : E) (hs : s ∈ V) (test : 𝔉 →L[ℂ] ℂ) :
      DifferentiableOn ℂ (fun t : ℂ => test (num (s + t • u))) (ball 0 2) :=
    (hn test).comp (hlined s).differentiableOn (hline s hs)
  have hda (s : E) (hs : s ∈ V) :
      AnalyticOnNhd ℂ (fun t : ℂ => den (s + t • u)) (ball 0 2) :=
    (hd.comp (hlined s).differentiableOn (hline s hs)).analyticOnNhd isOpen_ball
  have hfin (s : E) (hs : s ∈ V) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 2) :
      analyticOrderAt (fun t : ℂ => den (s + t • u)) z ≠ ⊤ :=
    (hda s hs).analyticOrderAt_ne_top_of_isPreconnected
      (convex_ball (0 : ℂ) 2).isPreconnected hbr hz
      (((hda s hs) r hbr).analyticOrderAt_eq_zero.mpr (hcircle s hs r hsr) ▸ ENat.zero_ne_top)
  -- division of every test along every slice
  have hdiv (s : E) (hs : s ∈ V) (test : 𝔉 →L[ℂ] ℂ) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 2) :
      AnalyticallyDividesAt (fun t : ℂ => den (s + t • u))
        (fun t : ℂ => test (num (s + t • u))) z := by
    apply analyticallyDividesAt_of_eval F G rho hsmooth hcalc hN hrho R L hL isOpen_ball
      (fun t : ℂ => num (s + t • u)) (hnl s hs) ⟨z, hz⟩ _ (hda s hs z hz) (hfin s hs z hz)
      _ test
    intro y
    refine ⟨fun t => Φ (s + t • u) y,
      ((hΦ y).comp (hlined s).differentiableOn (hline s hs)).analyticOnNhd isOpen_ball z hz, ?_⟩
    filter_upwards [isOpen_ball.mem_nhds hz] with t ht
    exact heq _ (hline s hs ht) y
  -- the holomorphic quotients of the tests
  let b (test : 𝔉 →L[ℂ] ℂ) : E → ℂ := circleDivision den (fun s => test (num s)) u r
  have hb (test : 𝔉 →L[ℂ] ℂ) : DifferentiableOn ℂ (b test) V :=
    differentiableOn_circleDivision hU hd (hn test) u hr
      (fun s hs z hz => ⟨hline s hs (mem_ball.mpr ((mem_sphere.mp hz).trans_lt hr2)),
        hcircle s hs z hz⟩)
  have hmul (test : 𝔉 →L[ℂ] ℂ) (s : E) (hs : s ∈ V) : den s * b test s = test (num s) :=
    mul_circleDivision_eq (num := fun t => test (num t)) hd u s hr hr2 (hline s hs)
      (hcircle s hs) (fun z hz => hdiv s hs test z hz)
  -- the Taylor quotient on the slice through `s`
  let k (s : E) : ℕ := analyticOrderNatAt (fun t : ℂ => den (s + t • u)) 0
  let v (s : E) : 𝔉 := if hs : s ∈ V then
      (iteratedDeriv (k s) (fun t : ℂ => den (s + t • u)) 0 / ((k s).factorial : ℂ))⁻¹ •
        taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL isOpen_ball
          (fun t : ℂ => num (s + t • u)) (hnl s hs) (k s) ⟨0, h0⟩
    else 0
  have hv (s : E) (hs : s ∈ V) (test : 𝔉 →L[ℂ] ℂ) {χ : ℂ → ℂ} (hχ : AnalyticAt ℂ χ 0)
      (hχeq : (fun t : ℂ => test (num (s + t • u))) =ᶠ[𝓝 0]
        (fun t : ℂ => den (s + t • u)) * χ) :
      test (v s) = χ 0 := by
    have hk : analyticOrderAt (fun t : ℂ => den (s + t • u)) 0 = (k s : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt (hfin s hs 0 h0)).symm
    obtain ⟨h1, h2⟩ := iteratedDeriv_eq_mul_of_analyticOrderAt_eq (hda s hs 0 h0) hχ hk hχeq
    have hfac : ((k s).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [v, dite_eq_left hs, map_smul, apply_taylorCoefficient, smul_eq_mul, h1]
    field_simp
  refine ⟨V, hVU, hVo, hsV, v, fun test => (hb test).congr fun s hs => ?_, fun s hs => ?_⟩
  · -- `test ∘ v` is the holomorphic quotient `b test`
    let O : Set ℂ := (fun t : ℂ => s + t • u) ⁻¹' V
    have hOo : IsOpen O := hVo.preimage (hlined s).continuous
    have h0O : (0 : ℂ) ∈ O := by simpa [O] using hs
    have hcomp : AnalyticAt ℂ (fun t : ℂ => b test (s + t • u)) 0 :=
      ((hb test).comp (hlined s).differentiableOn (fun t ht => ht)).analyticOnNhd hOo 0 h0O
    refine (hv s hs test hcomp ?_).trans (by simp)
    filter_upwards [hOo.mem_nhds h0O] with t ht
    exact (hmul test _ ht).symm
  · -- the underlying function of `v s` is `Φ s`
    funext y
    rw [← UniformGrowthFrechetSpace.evalCLM_apply F G rho hsmooth hcalc hN hrho R L y]
    have hχ : AnalyticAt ℂ (fun t : ℂ => Φ (s + t • u) y) 0 :=
      ((hΦ y).comp (hlined s).differentiableOn (hline s hs)).analyticOnNhd isOpen_ball 0 h0
    refine (hv s hs _ hχ ?_).trans (by simp)
    filter_upwards [isOpen_ball.mem_nhds h0] with t ht
    rw [UniformGrowthFrechetSpace.evalCLM_apply]
    exact heq _ (hline s hs ht) y

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
