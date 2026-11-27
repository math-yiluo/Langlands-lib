import Langlands.Global.AdelicLeadingCuspidalInjectivityReduction
import Langlands.Global.AdelicShiftedMaximalDecay
import Langlands.Global.AdelicCuspidalExponentAscentReduction
import Langlands.GroupScheme.Rational.ArthurRelativeCombinatorics
import Langlands.LinearAlgebra.ArthurCombinatoricsSigma
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof
import Mathlib.LinearAlgebra.Lagrange

/-! # Bounds for cuspidal components with a negative exponent along a maximal parabolic

For `R = Q ∪ {β}`, a function on `U_Q(𝔸) M_Q(F) \ G(𝔸)` which is cuspidal along `Q` and has a
single unnormalized exponent `λ` along `Q` with `⟨Re λ, β^∨⟩ < 0` is bounded on Siegel regions
of the Levi `M_R`. The proof interpolates the exponent polynomial along the line of `𝔄_Q` in the
direction of the projection of `β^∨`, and bounds the interpolation values by the rapid decay of
cuspidal functions on Siegel regions of `M_Q`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open Polynomial

namespace Langlands.Analysis

/-- On a half-line `[h₀, ∞)`, `e^{-δ t} (1 + |t|)^n` is bounded for `δ > 0`. -/
theorem exists_exp_mul_one_add_abs_pow_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (h₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, h₀ ≤ t → Real.exp (-δ * t) * (1 + |t|) ^ n ≤ C := by
  let K := 1 + |h₀|
  have hK : 1 ≤ K := le_add_of_nonneg_right (abs_nonneg _)
  refine ⟨Real.exp (-δ * h₀) * K ^ n * (n.factorial * Real.exp δ / δ ^ n), by positivity, ?_⟩
  intro t ht
  set s := t - h₀ with hs
  have hs0 : 0 ≤ s := sub_nonneg.mpr ht
  have habs : 1 + |t| ≤ K * (1 + s) := by
    have h1 : |t| ≤ |h₀| + s := by
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self h₀]
      · rw [abs_of_neg h]; linarith [neg_abs_le h₀]
    nlinarith [abs_nonneg h₀]
  have hpow : (1 + s) ^ n ≤ n.factorial * Real.exp δ / δ ^ n * Real.exp (δ * s) := by
    have h := Real.pow_div_factorial_le_exp (x := δ * (1 + s)) (by positivity) n
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    rw [show Real.exp (δ * (1 + s)) = Real.exp δ * Real.exp (δ * s) by
      rw [← Real.exp_add]; ring_nf] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos δ, Real.exp_pos (δ * s), pow_pos hδ n]
  calc Real.exp (-δ * t) * (1 + |t|) ^ n ≤ Real.exp (-δ * t) * (K * (1 + s)) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) habs n) (Real.exp_pos _).le
    _ = Real.exp (-δ * h₀) * K ^ n * (Real.exp (-δ * s) * (1 + s) ^ n) := by
        rw [mul_pow, hs, show -δ * t = -δ * h₀ + -δ * (t - h₀) by ring, Real.exp_add]; ring
    _ ≤ Real.exp (-δ * h₀) * K ^ n * (Real.exp (-δ * s) *
          (n.factorial * Real.exp δ / δ ^ n * Real.exp (δ * s))) := by
        gcongr
    _ = Real.exp (-δ * h₀) * K ^ n * (n.factorial * Real.exp δ / δ ^ n) := by
        rw [show Real.exp (-δ * s) * (n.factorial * Real.exp δ / δ ^ n * Real.exp (δ * s)) =
          n.factorial * Real.exp δ / δ ^ n * (Real.exp (-δ * s) * Real.exp (δ * s)) by ring,
          ← Real.exp_add, show -δ * s + δ * s = 0 by ring, Real.exp_zero, mul_one]

/-- A complex polynomial grows at most like `(1 + |t|)^{deg}` on the real line. -/
theorem exists_norm_eval_le (p : ℂ[X]) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, ‖p.eval (t : ℂ)‖ ≤ A * (1 + |t|) ^ p.natDegree := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun t => ?_⟩
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc |t| ^ i ≤ (1 + |t|) ^ i := pow_le_pow_left₀ (abs_nonneg _) (by linarith) i
    _ ≤ (1 + |t|) ^ p.natDegree :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **Lagrange interpolation against a decaying exponential.** For `δ > 0`, a degree bound `n`
and a half-line `[h₀, ∞)`, there is `M` such that every complex polynomial `q` of degree at most
`n` satisfies `e^{-δ t} |q(t)| ≤ M ∑_{i ≤ n} |q(i)|` for `t ≥ h₀`. -/
theorem exists_exp_mul_norm_eval_le_sum (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (h₀ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ℂ[X], q.natDegree ≤ n → ∀ t : ℝ, h₀ ≤ t →
      Real.exp (-δ * t) * ‖q.eval (t : ℂ)‖ ≤
        M * ∑ i ∈ Finset.range (n + 1), ‖q.eval ((i : ℕ) : ℂ)‖ := by
  let s := Finset.range (n + 1)
  let v : ℕ → ℂ := fun i => (i : ℂ)
  have hvs : Set.InjOn v s := fun i _ j _ h => by simpa [v] using h
  have hbasis (i : ℕ) := exists_norm_eval_le (Lagrange.basis s v i)
  choose A hA hAb using hbasis
  have hexp (i : ℕ) := exists_exp_mul_one_add_abs_pow_le (Lagrange.basis s v i).natDegree hδ h₀
  choose E hE hEb using hexp
  let M := ∑ i ∈ s, A i * E i
  refine ⟨M, Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (hE i), fun q hq t ht => ?_⟩
  have hdeg : q.degree < (s.card : WithBot ℕ) := by
    rw [Finset.card_range]
    exact (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hq)).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
  have hq' := Lagrange.eq_interpolate hvs hdeg
  have heval : q.eval (t : ℂ) = ∑ i ∈ s, q.eval (v i) * (Lagrange.basis s v i).eval (t : ℂ) := by
    conv_lhs => rw [hq']
    rw [Lagrange.interpolate_apply, eval_finsetSum]
    simp only [eval_mul, eval_C]
  have hterm (i : ℕ) : Real.exp (-δ * t) * ‖(Lagrange.basis s v i).eval (t : ℂ)‖ ≤ A i * E i := by
    calc Real.exp (-δ * t) * ‖(Lagrange.basis s v i).eval (t : ℂ)‖
        ≤ Real.exp (-δ * t) * (A i * (1 + |t|) ^ (Lagrange.basis s v i).natDegree) :=
          mul_le_mul_of_nonneg_left (hAb i t) (Real.exp_pos _).le
      _ = A i * (Real.exp (-δ * t) * (1 + |t|) ^ (Lagrange.basis s v i).natDegree) := by ring
      _ ≤ A i * E i := mul_le_mul_of_nonneg_left (hEb i t ht) (hA i)
  have hsum : ∑ i ∈ s, ‖q.eval (v i)‖ * (A i * E i) ≤
      M * ∑ i ∈ s, ‖q.eval (v i)‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact Finset.single_le_sum (f := fun j => A j * E j)
      (fun j _ => mul_nonneg (hA j) (hE j)) hi
  calc Real.exp (-δ * t) * ‖q.eval (t : ℂ)‖
      ≤ Real.exp (-δ * t) * ∑ i ∈ s, ‖q.eval (v i)‖ * ‖(Lagrange.basis s v i).eval (t : ℂ)‖ := by
        rw [heval]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans_eq ?_) (Real.exp_pos _).le
        simp only [norm_mul]
    _ = ∑ i ∈ s, ‖q.eval (v i)‖ *
          (Real.exp (-δ * t) * ‖(Lagrange.basis s v i).eval (t : ℂ)‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ∑ i ∈ s, ‖q.eval (v i)‖ * (A i * E i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (norm_nonneg _)
    _ ≤ M * ∑ i ∈ s, ‖q.eval (v i)‖ := hsum

/-- On a line `t ↦ t • H`, a polynomial function of degree at most `n`
(`polynomialFunctions`) is a complex polynomial of degree at most `n` in `t`. -/
theorem exists_polynomial_natDegree_le_eval_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {f : V → ℂ} (hf : f ∈ Langlands.Global.polynomialFunctions V n) (H : V) :
    ∃ q : ℂ[X], q.natDegree ≤ n ∧ ∀ t : ℝ, f (t • H) = q.eval (t : ℂ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, ℓ, rfl⟩ := hf
    refine ⟨Polynomial.C (∏ j, ((ℓ j H : ℝ) : ℂ)) * X ^ k,
      (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le k).trans hk), fun t => ?_⟩
    simp only [map_smul, smul_eq_mul, Complex.ofReal_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, eval_mul, eval_C, eval_pow, eval_X]
    ring
  | zero => exact ⟨0, by simp, fun t => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨q₁, hd₁, h₁⟩ := hf
    obtain ⟨q₂, hd₂, h₂⟩ := hg
    exact ⟨q₁ + q₂, (natDegree_add_le _ _).trans (max_le hd₁ hd₂), fun t => by simp [h₁, h₂]⟩
  | smul c f _ hf =>
    obtain ⟨q, hd, hq⟩ := hf
    exact ⟨Polynomial.C c * q, (natDegree_C_mul_le _ _).trans hd, fun t => by simp [hq]⟩

end Langlands.Analysis

open CategoryTheory AlgebraicGeometry NumberField Set TensorProduct
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus AdelicSiegelFactors
  RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "aG" => positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T)

section Roots

omit [NumberField F] in
/-- For a simple root `β` of `R ⊇ Q`, the projection `w` of `β^∨` to `𝔞_Q` along the coroots of
`Q`: the roots of `Q` vanish on `w`, the characters of `M_R` vanish on `w`, the characters of
`M_Q` pair with `w` as with `β^∨`, and `β^∨ - w` lies in the span of the coroots of `Q`. -/
theorem exists_corootProjection {Q R : Idx} (hQR : Q ≤ R) (β : relativeRoots 𝓕.i)
    (hβ : β.1 ∈ R.1) :
    ∃ w : V 𝓕.T, w ∈ rootAnnihilator 𝓕.T Q.1 ∧
      (∀ x ∈ corootAnnihilator 𝓕.i 𝓕.coroots R.1, pair 𝓕.T x w = 0) ∧
      (∀ x ∈ corootAnnihilator 𝓕.i 𝓕.coroots Q.1,
        pair 𝓕.T x w = pair 𝓕.T x ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β)) ∧
      𝓕.coroots.realCoroot β - w ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf Q.1) := by
  have hc : IsCompl (rootAnnihilator 𝓕.T Q.1) (Submodule.span ℝ (𝓕.coroots.realCorootsOf Q.1)) :=
    ((standardLeviRealDecomposition F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit
      𝓕.ν 𝓕.generic 𝓕.coroots).2.2.2 Q.1 R.1 hQR R.2).2.1
  have hmem : 𝓕.coroots.realCoroot β ∈
      rootAnnihilator 𝓕.T Q.1 ⊔ Submodule.span ℝ (𝓕.coroots.realCorootsOf Q.1) := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, u, hu, hwu⟩ := Submodule.mem_sup.mp hmem
  have hker : ∀ (J : Set (characterLattice 𝓕.T)) (x : Vstar 𝓕.T),
      x ∈ corootAnnihilator 𝓕.i 𝓕.coroots J →
      Submodule.span ℝ (𝓕.coroots.realCorootsOf J) ≤ LinearMap.ker (pair 𝓕.T x) := by
    intro J x hx
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_corootAnnihilator 𝓕.i 𝓕.coroots J x).mp hx b hb
  have hsub : 𝓕.coroots.realCorootsOf Q.1 ⊆ 𝓕.coroots.realCorootsOf R.1 := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, hQR hb, rfl⟩
  have h1 : 𝓕.coroots.realCoroot β ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf R.1) :=
    Submodule.subset_span ⟨β, hβ, rfl⟩
  have h2 : u ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf R.1) := Submodule.span_mono hsub hu
  have hw' : w = 𝓕.coroots.realCoroot β - u := eq_sub_of_add_eq hwu
  have hwR : w ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf R.1) := by
    rw [hw']
    exact Submodule.sub_mem _ h1 h2
  refine ⟨w, hw, fun x hx => hker R.1 x hx hwR, fun x hx => ?_, ?_⟩
  · have hu0 : pair 𝓕.T x u = 0 := hker Q.1 x hx hu
    have hβeq : (1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β = w + u := hwu.symm
    rw [hβeq, map_add, hu0, add_zero]
  · rw [hw', sub_sub_cancel]
    exact hu

omit [NumberField F] in
/-- **A fundamental weight as a nonnegative combination of roots.** For a simple root `β` of a
standard index `R` there is a real linear form `ϖ` on `𝔞_0`, a combination of the simple roots
of `R` with nonnegative coefficients (the row of `β` in the inverse Cartan matrix of `R`), with
`ϖ(β^∨) = 1` and `ϖ(α^∨) = 0` for the other simple roots `α` of `R`. In particular `ϖ` is
bounded below on the region where the roots of `R` are bounded below, and `β` lies in the span
of `ϖ` and the other simple roots of `R`. -/
theorem exists_weightForm (R : Idx) {β : relativeRoots 𝓕.i} (hβ : β.1 ∈ R.1) :
    ∃ ϖ : Vstar 𝓕.T,
      pair 𝓕.T ϖ (𝓕.coroots.realCoroot β) = 1 ∧
      (∀ α : relativeRoots 𝓕.i, α.1 ∈ R.1 → α.1 ≠ β.1 →
        pair 𝓕.T ϖ (𝓕.coroots.realCoroot α) = 0) ∧
      (∃ c : ℝ, 0 ≤ c ∧ ∀ (v : V 𝓕.T) (B : ℝ), 0 ≤ B →
        (∀ ρ₁ ∈ R.1, -B ≤ pair 𝓕.T ((1 : ℝ) ⊗ₜ[ℤ] ρ₁) v) → -(c * B) ≤ pair 𝓕.T ϖ v) ∧
      (1 : ℝ) ⊗ₜ[ℤ] β.1 ∈ Submodule.span ℝ
        (insert ϖ ((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' (R.1 \ {β.1}))) := by
  let hG := 𝓕.connectedReductive
  let hi := 𝓕.maximalSplit
  let hν := 𝓕.generic
  let D := 𝓕.coroots
  have := ArthurRelative.finite_indivisibleRoots hG hi
  let Θ := ArthurRelative.standardIndex hG hi 𝓕.ν R.1
  have hΘ := ArthurRelative.standardIndex_subset_support hG hi D hν R.1
  have hβi : β.1 ∈ RelativeRoot.indivisibleRoots 𝓕.i :=
    ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots hG hi 𝓕.ν (R.2 hβ)
  let β' : RelativeRoot.indivisibleRoots 𝓕.i := ⟨β.1, hβi⟩
  have hβΘ : β' ∈ Θ := (ArthurRelative.mem_standardIndex hG hi 𝓕.ν).mpr ⟨R.2 hβ, hβ⟩
  let P := ArthurRelative.rootPairing hG hi D
  let W := (ArthurCombinatorics.cartanBlock P Θ)⁻¹
  let bβ : Θ := ⟨β', hβΘ⟩
  let ϖ : Vstar 𝓕.T := ∑ k : Θ, W bβ k •
    ((1 : ℝ) ⊗ₜ[ℤ] ((k : RelativeRoot.indivisibleRoots 𝓕.i) : characterLattice 𝓕.T))
  have hW : ∀ k, 0 ≤ W bβ k := fun k =>
    ArthurCombinatorics.cartanBlock_inv_nonneg' (ArthurRelative.base hG hi hν D) hΘ bβ k
  have hkR (k : Θ) : ((k : RelativeRoot.indivisibleRoots 𝓕.i) : characterLattice 𝓕.T) ∈ R.1 :=
    ((ArthurRelative.mem_standardIndex hG hi 𝓕.ν).mp k.2).2
  have hroot (k : RelativeRoot.indivisibleRoots 𝓕.i) (v : V 𝓕.T) :
      (ArthurRelative.rootPairing hG hi D).root' k (ArthurRelative.toCorootSpan hG hi D v) =
        pair 𝓕.T ((1 : ℝ) ⊗ₜ[ℤ] (k : characterLattice 𝓕.T)) v := by
    have h := ArthurRelative.eval_sub_toCorootSpan hG hi D k.2.1 v
    rw [map_sub, sub_eq_zero, eval_eq_pair] at h
    rw [h]
    rfl
  have hpair (v : V 𝓕.T) :
      pair 𝓕.T ϖ v = ArthurRelative.weight hG hi 𝓕.ν D R.1 β.1 v := by
    have h := ArthurRelative.weight_coe hG hi 𝓕.ν D R.1 β' v
    rw [ArthurCombinatorics.weightCoordinate_eq_sum hβΘ] at h
    change pair 𝓕.T ϖ v = ArthurRelative.weight hG hi 𝓕.ν D R.1 β' v
    rw [h]
    simp only [ϖ, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hroot]
  refine ⟨ϖ, ?_, ?_, ?_, ?_⟩
  · rw [hpair, ArthurRelative.weight_coroot hG hi D hν R.2 hβ β hβ]
    simp
  · intro α hα hne
    rw [hpair, ArthurRelative.weight_coroot hG hi D hν R.2 hβ α hα]
    simp [Ne.symm hne]
  · refine ⟨∑ k : Θ, W bβ k, Finset.sum_nonneg fun k _ => hW k, fun v B hB hlo => ?_⟩
    simp only [ϖ, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := mul_le_mul_of_nonneg_left (hlo _ (hkR k)) (hW k)
    linarith
  · have hdiag : (1 : ℝ) / 2 ≤ W bβ bβ :=
      ArthurCombinatorics.half_le_cartanBlock_inv_self (ArthurRelative.base hG hi hν D) hΘ bβ
    have hpos : W bβ bβ ≠ 0 := by linarith
    have hsplit := (Finset.add_sum_erase Finset.univ (fun k : Θ => W bβ k •
      ((1 : ℝ) ⊗ₜ[ℤ] ((k : RelativeRoot.indivisibleRoots 𝓕.i) : characterLattice 𝓕.T))))
      (Finset.mem_univ bβ)
    let S := Submodule.span ℝ
      (insert ϖ ((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' (R.1 \ {β.1})))
    have hϖS : ϖ ∈ S := Submodule.subset_span (Set.mem_insert _ _)
    have hrest : ∑ k ∈ Finset.univ.erase bβ, W bβ k •
        ((1 : ℝ) ⊗ₜ[ℤ] ((k : RelativeRoot.indivisibleRoots 𝓕.i) : characterLattice 𝓕.T)) ∈ S := by
      refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine Set.mem_insert_of_mem _ ⟨_, ⟨hkR k, ?_⟩, rfl⟩
      intro hkβ
      apply (Finset.mem_erase.mp hk).1
      exact Subtype.ext (Subtype.ext hkβ)
    have hβeq : (1 : ℝ) ⊗ₜ[ℤ] β.1 = (W bβ bβ)⁻¹ • (ϖ - ∑ k ∈ Finset.univ.erase bβ, W bβ k •
        ((1 : ℝ) ⊗ₜ[ℤ] ((k : RelativeRoot.indivisibleRoots 𝓕.i) : characterLattice 𝓕.T))) := by
      rw [show ϖ = _ from hsplit.symm, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hpos,
        one_smul]
    rw [hβeq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hϖS hrest)

end Roots

section Line

omit [NumberField F] in
/-- The real functional of a sum of real cocharacters is the sum of the functionals. -/
theorem cocharacterFunctional_add (v v' : V 𝓕.T) :
    cocharacterFunctional (F := F) (v + v') = cocharacterFunctional v + cocharacterFunctional v' := by
  apply AddMonoidHom.ext
  intro χ
  change pair 𝓕.T (1 ⊗ₜ[ℤ] χ) (v + v') = pair 𝓕.T (1 ⊗ₜ[ℤ] χ) v + pair 𝓕.T (1 ⊗ₜ[ℤ] χ) v'
  rw [map_add]

/-- A real cocharacter annihilated by the roots of `Q` is the logarithm of a positive torus point
whose image in `G(𝔸)` is the image of a point of the positive split component `𝔄_Q`. -/
theorem exists_splitComponent_of_log (Q : Idx) {v : V 𝓕.T} (hv : v ∈ rootAnnihilator 𝓕.T Q.1) :
    ∃ τ : intrinsicSubgroup F 𝓕.T, characterLog F 𝓕.T.toGrp τ.val = cocharacterFunctional v ∧
      ∃ s ∈ 𝓕.positiveSplitComponent Q, map F (𝓕.P Q) G (𝓕.p Q) s = aG τ := by
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  obtain ⟨x, hx, hlog⟩ := exists_characterLog_eq hT (cocharacterFunctional v)
  have hQ : ∀ ρ₁ ∈ Q.1, Lie.characterValue ρ₁ x = 1 := by
    intro ρ₁ hρ₁
    refine characterValue_eq_one_of_characterLog_eq_zero hx ?_
    have h := congrArg (fun ℓ : RealCharacterDual F 𝓕.T.toGrp => ℓ ρ₁) hlog
    rw [h, cocharacterFunctional_apply, ← eval_eq_pair]
    exact (mem_rootAnnihilator _ _).mp hv ρ₁ hρ₁
  obtain ⟨s, hs, hsmap⟩ := positiveTorusSplitComponent F G 𝓕 Q x hx hQ
  refine ⟨⟨x, hx⟩, hlog, s, hs, ?_⟩
  rw [hsmap]
  change _ = map F 𝓕.T.toGrp G (CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i) x
  rw [show CommGroupScheme.groupHom (𝟙 𝓕.T) = 𝟙 𝓕.T.toGrp from rfl, Category.id_comp]

/-- A point of `P_Q(𝔸)` with the image in `G(𝔸)` of a torus point `t` is the image of `t`. -/
theorem eq_map_torus_of_map_parabolic_eq {Q : Idx} {s : AdelicGroupPoints F (𝓕.P Q)}
    {t : AdelicGroupPoints F 𝓕.T.toGrp}
    (ht : map F (𝓕.P Q) G (𝓕.p Q) s = map F 𝓕.T.toGrp G 𝓕.i t) :
    s = map F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) t := by
  let := (𝓕.isCompatible Q).parabolic.isClosedSubgroup.mono
  have : Mono (𝓕.p Q).hom.hom := Over.mono_of_mono_left _
  have h1 : map F (𝓕.P Q) G (𝓕.p Q) s =
      map F (𝓕.P Q) G (𝓕.p Q) (map F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) t) := by
    rw [ht, ← map_comp_apply_of_hom, Category.assoc, 𝓕.torus_comp]
  simp only [map_apply, GroupScheme.affinePointsTarget_apply] at h1
  exact (cancel_mono _).mp h1

end Line

section Bound

variable {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "B₀" => (Subtype.mk ∅ (empty_subset (simpleRelativeRoots 𝓕.i 𝓕.ν)) : Idx)
local notation "height" => adelicHeight F G rho

/-- **Boundedness of a cuspidal exponent component along a maximal parabolic of `M_R`.** Let
`Q ⊆ R` with `R = Q ∪ {β}`, `β ∉ Q`, and let `Φ` be a set of real linear forms on `𝔞_0`,
annihilated by the coroots of `R`, which together with the simple roots of `R` spans `𝔞_0^*`.
Let `c` be continuous on `G(𝔸)`, smooth on the archimedean slices, left invariant under `P_0(F)`
and `U_Q(𝔸)`, right invariant under an open finite level, cuspidal along `Q` (vanishing
constant terms along `Q \ {γ}`, `γ ∈ Q`), with derivative words of common polynomial growth, and
with unnormalized exponent `λ` along `Q` such that `⟨Re λ, β^∨⟩ < 0`. Then `c` is bounded on the
region of points `p a k` with `p` in a compact subset of `P_0(𝔸)`, the normalized adelic norms
of the simple roots of `R` at `a` at least a fixed `b > 0`, the forms of `Φ` bounded by `B ≥ 0`
at the logarithm of `a`, `k` in a compact set and the finite part in a compact set. -/
def CuspidalExponentLineBoundStatement : Prop :=
  0 < N →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (Q R : Idx) (β : relativeRoots 𝓕.i), β.1 ∉ Q.1 → insert β.1 Q.1 = R.1 →
  ∀ (Φ : Set (Vstar 𝓕.T)),
    Submodule.span ℝ (((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' R.1) ∪ Φ) = ⊤ →
    Φ ⊆ corootAnnihilator 𝓕.i 𝓕.coroots R.1 →
  ∀ (b : ℝ≥0ˣ) (B : ℝ), 0 ≤ B →
  ∀ (Ω K : Set A), IsCompact Ω → IsCompact K →
    Ω ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A) →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (lam : ComplexCharacterParameter F (𝓕.P Q)) (c : A → ℂ), Continuous c →
  (∀ y : Gf, ContMDiff IG IC ∞ (fun x : G∞ => c (pair F G x y))) →
  (∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, c (r * x) = c x) →
  𝓕.IsRadicalInvariant Q c →
  (∀ l ∈ L, ∀ x, c (x * ofFinite F G l) = c x) →
  (∀ ρ₁ ∈ Q.1, 𝓕.constantTerm (𝓕.removeSimpleRoot Q ρ₁) c = 0) →
  ∀ Rg : ℝ, 0 ≤ Rg →
  (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, ‖adelicIteratedDirectionalValue hG s c x‖ ≤ C * height x ^ Rg) →
  𝓕.HasUnnormalizedExponent Q lam c →
  pair 𝓕.T (𝓕.realExponent Q lam) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) < 0 →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Ω, ∀ (a : intrinsicSubgroup F 𝓕.T) (H : V 𝓕.T),
    cocharacterFunctional H = characterLog F 𝓕.T.toGrp a.val →
    (∀ ρ₁ ∈ R.1, b ≤ normCharacter F 𝓕.T ρ₁ a) →
    (∀ φ ∈ Φ, |pair 𝓕.T φ H| ≤ B) →
    ∀ k ∈ K, finite F G (p * aG a * k) ∈ Yf →
    ‖c (p * aG a * k)‖ ≤ C

theorem cuspidalExponentLineBound : 𝓕.CuspidalExponentLineBoundStatement hG rho := by
  intro hN
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro Q R β hβQ hins Φ hspan hΦR b B hB Ω K hΩ hK hΩP Yf hYf L hL lam c hc hcS hcR hcU hcL
    hcusp Rg hRg hgrowth hexp hneg
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  have hβR : β.1 ∈ R.1 := hins ▸ Set.mem_insert _ _
  have hQR : Q ≤ R := fun x hx => hins ▸ Set.mem_insert_of_mem _ hx
  obtain ⟨w, hwQ, hwR, hwβ, hwu⟩ := 𝓕.exists_corootProjection hQR β hβR
  obtain ⟨ϖ, hϖβ, hϖα, ⟨cϖ, hcϖ, hϖlow⟩, hβspan⟩ := 𝓕.exists_weightForm R hβR
  have hϖw : pair 𝓕.T ϖ w = 1 := by
    have h0 : ∀ u ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf Q.1), pair 𝓕.T ϖ u = 0 := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨α, hα, rfl⟩ := hx
        exact hϖα α (hQR hα) (fun h => hβQ (h ▸ hα))
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul r x _ hx => rw [map_smul, hx, smul_zero]
    have h1 := h0 _ hwu
    rw [map_sub, hϖβ, sub_eq_zero] at h1
    exact h1.symm
  set δ := -pair 𝓕.T (𝓕.realExponent Q lam) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) with hδdef
  have hδ : 0 < δ := by linarith
  have hlamw : pair 𝓕.T (𝓕.realExponent Q lam) w = -δ := by
    rw [hwβ _ (𝓕.realExponent_mem_corootAnnihilator Q lam), hδdef, neg_neg]
  -- the line of split-component points with logarithm `t w`
  have hline (t : ℝ) := 𝓕.exists_splitComponent_of_log Q (Submodule.smul_mem _ t hwQ)
  choose τ hτlog x hx hxmap using hline
  have hxtorus (t : ℝ) : x t = map F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) (τ t).val :=
    𝓕.eq_map_torus_of_map_parabolic_eq ((hxmap t).trans (by
      change map F 𝓕.T.toGrp G (CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i) (τ t).val = _
      rw [show CommGroupScheme.groupHom (𝟙 𝓕.T) = 𝟙 𝓕.T.toGrp from rfl, Category.id_comp]))
  let H₀ : RealCharacterDual F (𝓕.P Q) :=
    realCharacterDualMap F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) (cocharacterFunctional w)
  have hxlog (t : ℝ) : characterLog F (𝓕.P Q) (x t) = t • H₀ := by
    rw [hxtorus, characterLog_map, hτlog]
    have hsm : cocharacterFunctional (F := F) (t • w) = t • cocharacterFunctional w := by
      apply AddMonoidHom.ext
      intro χ
      change pair 𝓕.T (1 ⊗ₜ[ℤ] χ) (t • w) = t * pair 𝓕.T (1 ⊗ₜ[ℤ] χ) w
      rw [map_smul, smul_eq_mul]
    rw [hsm, map_smul]
  have hinv (mu : ComplexCharacterParameter F (𝓕.P Q)) (y : AdelicGroupPoints F (𝓕.P Q)) :
      parameterPower F (𝓕.P Q) mu y * parameterPower F (𝓕.P Q) (-mu) y = 1 := by
    rw [← parameterPower_add, add_neg_cancel]
    simp [parameterPower]
  have hnormlam (t : ℝ) : ‖parameterPower F (𝓕.P Q) lam (x t)‖ = Real.exp (-δ * t) := by
    rw [hxtorus, norm_parameterPower_map_torus _ _ _ (t • w) (hτlog t)]
    congr 1
    change pair 𝓕.T (𝓕.realExponent Q lam) (t • w) = _
    rw [map_smul, smul_eq_mul, hlamw]
    ring
  have hnormneg (t : ℝ) : ‖parameterPower F (𝓕.P Q) (-lam) (x t)‖ = Real.exp (δ * t) := by
    have h := congrArg norm (hinv lam (x t))
    rw [norm_mul, hnormlam, norm_one] at h
    have hpos := Real.exp_pos (-δ * t)
    have hN : ‖parameterPower F (𝓕.P Q) (-lam) (x t)‖ = 1 / Real.exp (-δ * t) := by
      rw [eq_div_iff hpos.ne', mul_comm]
      exact h
    rw [hN, one_div, ← Real.exp_neg]
    ring_nf
  -- interpolation and the cuspidal bound
  obtain ⟨n, hn⟩ := hexp
  let Bb := max 0 (-Real.log ((b : ℝ≥0) : ℝ))
  have hBb : 0 ≤ Bb := le_max_left _ _
  obtain ⟨Mi, hMi, hinterp⟩ := Langlands.Analysis.exists_exp_mul_norm_eval_le_sum n hδ (-(cϖ * Bb))
  have hspanQ : Submodule.span ℝ (((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' Q.1) ∪
      insert ϖ Φ) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    have hsub : insert ϖ ((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' (R.1 \ {β.1})) ⊆
        ((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' Q.1) ∪ insert ϖ Φ := by
      rintro _ (rfl | ⟨χ₀, ⟨hχR, hχβ⟩, rfl⟩)
      · exact Or.inr (Set.mem_insert _ _)
      · refine Or.inl ⟨χ₀, ?_, rfl⟩
        rw [← hins] at hχR
        exact hχR.resolve_left hχβ
    rintro _ (⟨χ₀, hχ, rfl⟩ | hφ)
    · by_cases hχβ : χ₀ = β.1
      · subst hχβ
        exact Submodule.span_mono hsub hβspan
      · have hχQ : χ₀ ∈ Q.1 := by
          rw [← hins] at hχ
          exact hχ.resolve_left hχβ
        exact Submodule.subset_span (Or.inl ⟨χ₀, hχQ, rfl⟩)
    · exact Submodule.subset_span (Or.inr (Set.mem_insert_of_mem _ hφ))
  obtain ⟨CB, hCB, hBbound⟩ := 𝓕.relativeCuspidalRegionDecay hG rho hN Q (insert ϖ Φ) hspanQ b
    (max B n) (hB.trans (le_max_left _ _)) Ω K hΩ hK hΩP Yf hYf L hL c hc hcS hcR hcU hcL hcusp
    Rg hRg hgrowth 0
  refine ⟨Mi * ((n + 1) * (CB * Real.exp (δ * n))), by positivity, ?_⟩
  intro p hp a H hH hlo hΦ k hk hxY
  let h := pair 𝓕.T ϖ H
  have hlog (ρ₁ : characterLattice 𝓕.T) :
      logNormHom F 𝓕.T a.val ρ₁ = pair 𝓕.T ((1 : ℝ) ⊗ₜ[ℤ] ρ₁) H := by
    rw [← cocharacterFunctional_apply, hH]
    rfl
  have hh : -(cϖ * Bb) ≤ h := by
    refine hϖlow H Bb hBb fun ρ₁ hρ₁ => ?_
    rw [← hlog]
    have hb0 : 0 < ((b : ℝ≥0) : ℝ) := by exact_mod_cast b.ne_zero.bot_lt
    have hlower : Real.log ((b : ℝ≥0) : ℝ) ≤ logNormHom F 𝓕.T a.val ρ₁ :=
      Real.log_le_log hb0 (by exact_mod_cast Units.val_le_val.mpr (hlo ρ₁ hρ₁))
    have : -Real.log ((b : ℝ≥0) : ℝ) ≤ Bb := le_max_right _ _
    linarith
  -- the shifted points
  let as (t : ℝ) : intrinsicSubgroup F 𝓕.T := τ t * (τ (-h) * a)
  have haslog (t : ℝ) : characterLog F 𝓕.T.toGrp (as t).val =
      cocharacterFunctional (t • w + ((-h) • w + H)) := by
    simp only [as, Subgroup.coe_mul, characterLog_mul, hτlog, hH, cocharacterFunctional_add]
  have hash : as h = a := by
    apply Subtype.ext
    apply eq_of_characterLog_eq hT (as h).2 a.2
    rw [haslog, ← hH]
    congr 1
    rw [neg_smul, add_neg_cancel_left]
  have hpQ : p ∈ (map F (𝓕.P Q) G (𝓕.p Q)).toMonoidHom.range :=
    𝓕.range_map_le_of_le (empty_subset _) (hΩP hp)
  let g₀ := p * (aG (τ (-h) * a) * k)
  have hkey (t : ℝ) :
      c (map F (𝓕.P Q) G (𝓕.p Q) (x t) * g₀) = c (p * aG (as t) * k) := by
    have h1 := IsRadicalInvariant.splitComponent_mul_comm 𝓕 hcU ⟨x t, hx t⟩ hpQ
      (aG (τ (-h) * a) * k)
    change c (map F (𝓕.P Q) G (𝓕.p Q) (x t) * (p * (aG (τ (-h) * a) * k))) = _
    rw [h1, hxmap]
    simp only [as, map_mul, mul_assoc]
  obtain ⟨Pg, hPg, hPge⟩ := hn g₀
  obtain ⟨q, hqdeg, hqeval⟩ := Langlands.Analysis.exists_polynomial_natDegree_le_eval_smul hPg H₀
  have hq (t : ℝ) : c (p * aG (as t) * k) * parameterPower F (𝓕.P Q) (-lam) (x t) =
      q.eval (t : ℂ) := by
    rw [← hkey, ← hqeval, ← hxlog]
    exact hPge (x t) (hx t)
  -- the values at the nodes
  have hnode (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖q.eval ((i : ℕ) : ℂ)‖ ≤ CB * Real.exp (δ * n) := by
    have hqi := hq i
    push_cast at hqi
    rw [← hqi, norm_mul, hnormneg]
    have hin : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hreg : ‖c (p * aG (as i) * k)‖ ≤ CB := by
      have hHi : cocharacterFunctional ((i : ℝ) • w + ((-h) • w + H)) =
          characterLog F 𝓕.T.toGrp (as i).val := (haslog i).symm
      have hloi : ∀ ρ₁ ∈ Q.1, b ≤ normCharacter F 𝓕.T ρ₁ (as i) := by
        intro ρ₁ hρ₁
        have hτ1 (t : ℝ) : normCharacter F 𝓕.T ρ₁ (τ t) = 1 := by
          have h0 : Real.log ((normCharacter F 𝓕.T ρ₁ (τ t) : ℝ≥0) : ℝ) = 0 := by
            change characterLog F 𝓕.T.toGrp (τ t).val ρ₁ = 0
            rw [hτlog, cocharacterFunctional_apply, map_smul, smul_eq_mul, ← eval_eq_pair,
              (mem_rootAnnihilator _ _).mp hwQ ρ₁ hρ₁, mul_zero]
          have hpos : (0 : ℝ) < ((normCharacter F 𝓕.T ρ₁ (τ t) : ℝ≥0) : ℝ) := by
            exact_mod_cast (normCharacter F 𝓕.T ρ₁ (τ t)).ne_zero.bot_lt
          exact Units.ext (NNReal.eq (by simpa using Real.eq_one_of_pos_of_log_eq_zero hpos h0))
        simp only [as, Subgroup.coe_mul, map_mul, hτ1, one_mul]
        exact hlo ρ₁ (hQR hρ₁)
      have hΦi : ∀ φ ∈ insert ϖ Φ, |pair 𝓕.T φ ((i : ℝ) • w + ((-h) • w + H))| ≤ max B n := by
        rintro φ (rfl | hφ)
        · rw [map_add, map_add, map_smul, map_smul, hϖw, smul_eq_mul, smul_eq_mul, mul_one,
            mul_one]
          change |(i : ℝ) + (-h + h)| ≤ _
          rw [neg_add_cancel, add_zero, abs_of_nonneg (Nat.cast_nonneg _)]
          exact hin.trans (le_max_right _ _)
        · rw [map_add, map_add, map_smul, map_smul, hwR φ (hΦR hφ), smul_zero, smul_zero,
            zero_add, zero_add]
          exact (hΦ φ hφ).trans (le_max_left _ _)
      have hfin : finite F G (p * aG (as i) * k) ∈ Yf := by
        have h1 : finite F G (p * aG (as i) * k) = finite F G (p * aG a * k) := by
          simp only [map_mul, finite_positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T) hT, mul_one]
        rw [h1]
        exact hxY
      have := hBbound p hp (as i) _ hHi hloi hΦi k hk hfin
      simpa using this
    exact mul_le_mul hreg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hin hδ.le))
      (Real.exp_pos _).le hCB
  -- the value at `a`
  have hval : c (p * aG a * k) = parameterPower F (𝓕.P Q) lam (x h) * q.eval (h : ℂ) := by
    rw [← hq h, hash, mul_left_comm, hinv, mul_one]
  rw [hval, norm_mul, hnormlam]
  calc Real.exp (-δ * h) * ‖q.eval (h : ℂ)‖
      ≤ Mi * ∑ i ∈ Finset.range (n + 1), ‖q.eval ((i : ℕ) : ℂ)‖ := hinterp q hqdeg h hh
    _ ≤ Mi * ∑ _i ∈ Finset.range (n + 1), CB * Real.exp (δ * n) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hnode) hMi
    _ = Mi * ((n + 1) * (CB * Real.exp (δ * n))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end Bound

end Langlands.Global.StandardParabolicFamily
