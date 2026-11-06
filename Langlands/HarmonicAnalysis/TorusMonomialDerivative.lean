import Langlands.HarmonicAnalysis.TorusFourierDecay
import Langlands.Representation.Plancherel.RationalOrbitBasisInvariance

/-! # Angular derivatives along an integer torus monomial

For an integer matrix `a : J → K → ℤ`, the monomial map `finiteTorusMonomial a` sends
`z : K → Circle` to `(∏ₖ z_k^{a j k})_j`. For a smooth `Φ` on `J → Circle` and a point `y`,
the `k`-th angular derivative of `z ↦ Φ(finiteTorusMonomial a z · y)` is
`∑ⱼ a j k ∂ⱼΦ(finiteTorusMonomial a z · y)` (chain rule). Iterating, the iterated angular
derivatives of these functions are bounded uniformly in `y`. This supplies the derivative
bounds along the directions of `Im X(G)` in the proof of Waldspurger's Prop. VI.3.1, where
`Im X(G) → Im X(M)` is written in torus coordinates as such a monomial map.
-/

noncomputable section

open Langlands.Plancherel
open scoped ContDiff

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J K : Type*} [Fintype J] [Fintype K]

omit [Fintype J] in
/-- The integer monomial map is multiplicative. -/
theorem finiteTorusMonomial_mul (a : J → K → ℤ) (z w : K → Circle) :
    finiteTorusMonomial a (z * w) = finiteTorusMonomial a z * finiteTorusMonomial a w := by
  funext j
  simp only [finiteTorusMonomial, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

omit [Fintype J] in
/-- The integer monomial map is continuous. -/
theorem continuous_finiteTorusMonomial (a : J → K → ℤ) :
    Continuous (finiteTorusMonomial a) :=
  continuous_pi fun j => continuous_finsetProd _ fun k _ => (continuous_apply k).zpow (a j k)

/-- Translation followed by an integer monomial preserves smoothness:
`z ↦ Φ(finiteTorusMonomial a z · y)` is smooth for smooth `Φ`. -/
theorem isSmoothFiniteTorusFunction_comp_monomial_mul {Φ : (J → Circle) → ℂ}
    (hΦ : IsSmoothFiniteTorusFunction Φ) (a : J → K → ℤ) (y : J → Circle) :
    IsSmoothFiniteTorusFunction (fun z => Φ (finiteTorusMonomial a z * y)) := by
  obtain ⟨b, rfl⟩ := (isOpenQuotientMap_finiteTorusExp J).surjective y
  have ht : IsSmoothFiniteTorusFunction (fun w => Φ (w * finiteTorusExp b)) := by
    unfold IsSmoothFiniteTorusFunction
    have he : (fun w => Φ (w * finiteTorusExp b)) ∘ finiteTorusExp =
        (Φ ∘ finiteTorusExp) ∘ (fun x => x + b) := by
      funext x
      simp only [Function.comp_apply, finiteTorusExp_add]
    rw [he]
    exact hΦ.comp (contDiff_id.add contDiff_const)
  exact ht.comp_monomial a

variable [DecidableEq J]

/-- The angular derivative along the `k`-th direction of the monomial map `a`, acting on
functions on `J → Circle`: `∑ⱼ a j k ∂ⱼΦ`. -/
def monomialPartialDeriv (a : J → K → ℤ) (k : K) (Φ : (J → Circle) → ℂ) :
    (J → Circle) → ℂ :=
  fun y => ∑ j, (a j k : ℂ) * torusPartialDeriv j Φ y

omit [Fintype K] in
theorem isSmoothFiniteTorusFunction_monomialPartialDeriv {Φ : (J → Circle) → ℂ}
    (hΦ : IsSmoothFiniteTorusFunction Φ) (a : J → K → ℤ) (k : K) :
    IsSmoothFiniteTorusFunction (monomialPartialDeriv a k Φ) := by
  unfold IsSmoothFiniteTorusFunction monomialPartialDeriv
  have hj : ∀ j, ContDiff ℝ ∞ (fun x => (a j k : ℂ) * torusPartialDeriv j Φ (finiteTorusExp x)) :=
    fun j => contDiff_const.mul (isSmoothFiniteTorusFunction_torusPartialDeriv hΦ j)
  simpa only [Function.comp_def] using ContDiff.sum (s := Finset.univ) fun j _ => hj j

omit [Fintype K] in
theorem isSmoothFiniteTorusFunction_iterate_monomialPartialDeriv {Φ : (J → Circle) → ℂ}
    (hΦ : IsSmoothFiniteTorusFunction Φ) (a : J → K → ℤ) (k : K) (n : ℕ) :
    IsSmoothFiniteTorusFunction ((monomialPartialDeriv a k)^[n] Φ) := by
  induction n with
  | zero => simpa using hΦ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact isSmoothFiniteTorusFunction_monomialPartialDeriv ih a k

omit [Fintype J] [DecidableEq J] in
/-- The real lift of the monomial map is additive. -/
theorem finiteTorusMonomialLift_add_single [DecidableEq K] (a : J → K → ℤ) (x : K → ℝ)
    (k : K) (θ : ℝ) :
    finiteTorusMonomialLift a (x + Pi.single k θ) =
      finiteTorusMonomialLift a x + θ • fun j => (a j k : ℝ) := by
  funext j
  simp only [finiteTorusMonomialLift, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp only [Pi.single_eq_same]
    ring
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **Chain rule along a monomial**: the `k`-th angular derivative of
`z ↦ Φ(finiteTorusMonomial a z · y)` is `∑ⱼ a j k ∂ⱼΦ(finiteTorusMonomial a z · y)`. -/
theorem torusPartialDeriv_comp_monomial_mul [DecidableEq K] {Φ : (J → Circle) → ℂ}
    (hΦ : IsSmoothFiniteTorusFunction Φ) (a : J → K → ℤ) (y : J → Circle) (k : K)
    (z : K → Circle) :
    torusPartialDeriv k (fun z => Φ (finiteTorusMonomial a z * y)) z =
      monomialPartialDeriv a k Φ (finiteTorusMonomial a z * y) := by
  obtain ⟨x, rfl⟩ := (isOpenQuotientMap_finiteTorusExp K).surjective z
  obtain ⟨b, rfl⟩ := (isOpenQuotientMap_finiteTorusExp J).surjective y
  set v : J → ℝ := fun j => (a j k : ℝ)
  set u : J → ℝ := finiteTorusMonomialLift a x + b
  have hpt : ∀ θ : ℝ, finiteTorusMonomial a (finiteTorusExp x * finiteTorusExp (Pi.single k θ)) *
      finiteTorusExp b = finiteTorusExp (u + θ • v) := fun θ => by
    rw [← finiteTorusExp_add, ← finiteTorusExp_monomialLift, ← finiteTorusExp_add,
      finiteTorusMonomialLift_add_single]
    congr 1
    simp only [u, v]
    abel
  have hu : finiteTorusMonomial a (finiteTorusExp x) * finiteTorusExp b = finiteTorusExp u := by
    rw [← finiteTorusExp_monomialLift, ← finiteTorusExp_add]
  have hF : Differentiable ℝ (Φ ∘ finiteTorusExp) := hΦ.differentiable (by simp)
  have hL : HasDerivAt (fun θ : ℝ => u + θ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hcomp := (hF (u + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hL
  have hd : deriv (fun θ : ℝ => Φ (finiteTorusMonomial a
      (finiteTorusExp x * finiteTorusExp (Pi.single k θ)) * finiteTorusExp b)) 0 =
      fderiv ℝ (Φ ∘ finiteTorusExp) u v := by
    simp_rw [hpt]
    have := hcomp.deriv
    simpa only [zero_smul, add_zero, Function.comp_def] using this
  unfold torusPartialDeriv
  rw [hd, hu]
  unfold monomialPartialDeriv
  simp_rw [torusPartialDeriv_finiteTorusExp hΦ]
  have hv : v = ∑ j, (a j k : ℝ) • (Pi.single j (1 : ℝ) : J → ℝ) := by
    funext i
    simp [v, Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Complex.real_smul]
  push_cast
  rfl

/-- **Iterated chain rule along a monomial.** -/
theorem iterate_torusPartialDeriv_comp_monomial_mul [DecidableEq K] {Φ : (J → Circle) → ℂ}
    (hΦ : IsSmoothFiniteTorusFunction Φ) (a : J → K → ℤ) (y : J → Circle) (k : K) (n : ℕ) :
    (torusPartialDeriv k)^[n] (fun z => Φ (finiteTorusMonomial a z * y)) =
      fun z => ((monomialPartialDeriv a k)^[n] Φ) (finiteTorusMonomial a z * y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext z
    exact torusPartialDeriv_comp_monomial_mul
      (isSmoothFiniteTorusFunction_iterate_monomialPartialDeriv hΦ a k n) a y k z

/-- **Uniform bounds along a monomial**: for smooth `Φ` there is `M ≥ 0` bounding
`Φ(finiteTorusMonomial a z · y)` and all its `n`-th angular derivatives in `z`, uniformly in
`y`. -/
theorem exists_bound_comp_monomial_mul [DecidableEq K] {Φ : (J → Circle) → ℂ}
    (hΦ : IsSmoothFiniteTorusFunction Φ) (a : J → K → ℤ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ (y : J → Circle) (z : K → Circle),
        ‖Φ (finiteTorusMonomial a z * y)‖ ≤ M) ∧
      ∀ (y : J → Circle) (k : K) (z : K → Circle),
        ‖(torusPartialDeriv k)^[n] (fun z => Φ (finiteTorusMonomial a z * y)) z‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := exists_norm_le_of_isSmooth hΦ
  choose M hM using fun k => exists_norm_le_of_isSmooth
    (isSmoothFiniteTorusFunction_iterate_monomialPartialDeriv hΦ a k n)
  refine ⟨|M₀| + ∑ k, |M k|, by positivity, fun y z => ?_, fun y k z => ?_⟩
  · refine (hM₀ _).trans ((le_abs_self M₀).trans ?_)
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => abs_nonneg _)
  · rw [iterate_torusPartialDeriv_comp_monomial_mul hΦ a y k n]
    refine (hM k _).trans ((le_abs_self (M k)).trans ?_)
    refine le_add_of_nonneg_of_le (abs_nonneg _) ?_
    exact Finset.single_le_sum (f := fun k => |M k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k)

end Langlands.HarmonicAnalysis.TorusFourier
