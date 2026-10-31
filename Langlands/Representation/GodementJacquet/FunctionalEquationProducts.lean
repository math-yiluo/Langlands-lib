import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.LaurentTransport
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Mathlib.Topology.Algebra.Polynomial

/-!
# Finite sums of products of continuations and functional equations

Rational continuations of finite sums of products of functions, and the
combination of two families of normalized functional equations into one
equation for the sums of products, with product polynomials, product unit and
summed exponent.
-/

noncomputable section

namespace Langlands.GodementJacquet

open Filter Topology RankinSelberg

section Evaluation

/-- A denominator of a product does not vanish where both factor denominators
do not vanish. -/
theorem ratFunc_denom_mul_eval_ne_zero {A B : RatFunc ℂ} {x : ℂ}
    (hA : A.denom.eval x ≠ 0) (hB : B.denom.eval x ≠ 0) :
    (A * B).denom.eval x ≠ 0 := by
  intro h
  have h' := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd A B) h
  rw [Polynomial.eval_mul] at h'
  rcases mul_eq_zero.mp h' with h'' | h''
  exacts [hA h'', hB h'']

/-- A denominator of a sum does not vanish where both summand denominators do
not vanish. -/
theorem ratFunc_denom_add_eval_ne_zero {A B : RatFunc ℂ} {x : ℂ}
    (hA : A.denom.eval x ≠ 0) (hB : B.denom.eval x ≠ 0) :
    (A + B).denom.eval x ≠ 0 := by
  intro h
  have h' := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd A B) h
  rw [Polynomial.eval_mul] at h'
  rcases mul_eq_zero.mp h' with h'' | h''
  exacts [hA h'', hB h'']

/-- At a point where every factor denominator is nonzero, a finite sum of
products has nonzero denominator and evaluates termwise. -/
theorem ratFunc_sum_mul_eval {ι : Type*} (J : Finset ι) (A B : ι → RatFunc ℂ) (x : ℂ)
    (hA : ∀ j ∈ J, (A j).denom.eval x ≠ 0) (hB : ∀ j ∈ J, (B j).denom.eval x ≠ 0) :
    (∑ j ∈ J, A j * B j).denom.eval x ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) x (∑ j ∈ J, A j * B j) =
        ∑ j ∈ J, RatFunc.eval (RingHom.id ℂ) x (A j) *
          RatFunc.eval (RingHom.id ℂ) x (B j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    rw [Finset.forall_mem_insert] at hA hB
    obtain ⟨ih1, ih2⟩ := ih hA.2 hB.2
    have hAB := ratFunc_denom_mul_eval_ne_zero hA.1 hB.1
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    refine ⟨ratFunc_denom_add_eval_ne_zero hAB ih1, ?_⟩
    rw [RatFunc.eval_add (RingHom.id ℂ) x hAB ih1, RatFunc.eval_mul (RingHom.id ℂ) x hA.1 hB.1, ih2]

/-- Evaluation of a rational function is continuous at a point where its
denominator does not vanish. -/
theorem ratFunc_eval_continuousAt (R : RatFunc ℂ) {x : ℂ} (hx : R.denom.eval x ≠ 0) :
    ContinuousAt (fun y => RatFunc.eval (RingHom.id ℂ) y R) x := by
  have h : (fun y => RatFunc.eval (RingHom.id ℂ) y R) =
      fun y => R.num.eval y / R.denom.eval y := by
    funext y
    simp only [RatFunc.eval, Polynomial.eval₂_id]
  rw [h]
  exact (R.num.continuous.continuousAt).div R.denom.continuous.continuousAt hx

end Evaluation

section Continuation

/-- A finite sum of products of functions with rational continuations has the
corresponding sum of products as rational continuation. -/
theorem hasRationalContinuation_sum_mul {q : ℕ} {ι : Type*} (J : Finset ι)
    (f g : ι → ℂ → ℂ) (A B : ι → RatFunc ℂ)
    (hf : ∀ j ∈ J, HasRationalContinuation q (f j) (A j))
    (hg : ∀ j ∈ J, HasRationalContinuation q (g j) (B j)) :
    HasRationalContinuation q (fun s => ∑ j ∈ J, f j s * g j s) (∑ j ∈ J, A j * B j) :=
  RationalContinuationLinear.continuation_sum J (fun j s => f j s * g j s) (fun j => A j * B j)
    fun j hj => (hf j hj).mul (hg j hj)

end Continuation

section FunctionalEquation

/-- The spectral point is a homomorphism from addition to multiplication. -/
theorem spectralPoint_add {q : ℕ} (hq : 0 < q) (a b : ℂ) :
    spectralPoint q (a + b) = spectralPoint q a * spectralPoint q b := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [spectralPoint, neg_add]
  exact Complex.cpow_add _ _ hq0

/-- The spectral point is continuous in the complex parameter. -/
theorem continuous_spectralPoint {q : ℕ} (hq : 0 < q) :
    Continuous (fun s : ℂ => spectralPoint q s) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  exact continuous_neg.const_cpow (Or.inl hq0)

/-- Along a real ray, the zero set of a nonzero polynomial in the spectral point
is finite. The ray may run in either direction. -/
theorem finite_ray_zeros {q : ℕ} (hq : 1 < q) (s₀ : ℂ) (ε : ℝ) (hε : ε ≠ 0)
    {D : Polynomial ℂ} (hD : D ≠ 0) :
    {t : ℝ | D.eval (spectralPoint q (s₀ + ((ε * t : ℝ) : ℂ))) = 0}.Finite := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hinj : Function.Injective (fun t : ℝ => spectralPoint q (s₀ + ((ε * t : ℝ) : ℂ))) := by
    intro t u h
    simp only [spectralPoint_add hq0] at h
    have h' := mul_left_cancel₀ (spectralPoint_ne_zero_of_pos hq0 s₀) h
    have h'' := spectralPoint_ofReal_injective hq h'
    exact mul_left_cancel₀ hε h''
  exact (Polynomial.finite_setOfPred_isRoot hD).preimage hinj.injOn

/-- Two families of normalized functional equations with trivial central scalar
and zero sign exponent combine into one equation for the finite sums of
products, with product polynomials, product unit and summed exponent. The
summands need not share poles with the sums. -/
theorem normalizedFunctionalEquation_sum_mul {q : ℕ} (hq : 1 < q) {ι : Type*}
    (J : Finset ι) {P₀ Pd₀ P₁ Pd₁ : Polynomial ℂ} {c₀ c₁ : ℂˣ} {m₀ m₁ : ℤ}
    (R₀ RD₀ R₁ RD₁ : ι → RatFunc ℂ)
    (h₀ : ∀ j ∈ J, NormalizedFunctionalEquation q P₀ Pd₀ 1 c₀ 0 m₀ (R₀ j) (RD₀ j))
    (h₁ : ∀ j ∈ J, NormalizedFunctionalEquation q P₁ Pd₁ 1 c₁ 0 m₁ (R₁ j) (RD₁ j)) :
    NormalizedFunctionalEquation q (P₀ * P₁) (Pd₀ * Pd₁) 1 (c₀ * c₁) 0 (m₀ + m₁)
      (∑ j ∈ J, R₀ j * R₁ j) (∑ j ∈ J, RD₀ j * RD₁ j) := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  intro s₀ hR hRD
  set x : ℂ → ℂ := fun s => spectralPoint q s with hx
  set L : ℂ → ℂ := fun s => (Pd₀ * Pd₁).eval (x (1 - s)) *
    RatFunc.eval (RingHom.id ℂ) (x (1 - s)) (∑ j ∈ J, RD₀ j * RD₁ j) with hL
  set Rt : ℂ → ℂ := fun s => ((1 : ℂˣ) : ℂ) ^ 0 * epsilonMonomial q (c₀ * c₁) (m₀ + m₁) s *
    ((P₀ * P₁).eval (x s) * RatFunc.eval (RingHom.id ℂ) (x s) (∑ j ∈ J, R₀ j * R₁ j))
    with hRt
  change L s₀ = Rt s₀
  have hxc : Continuous x := continuous_spectralPoint hq0
  have hLc : ContinuousAt L s₀ := by
    have h1 : ContinuousAt (fun s : ℂ => x (1 - s)) s₀ :=
      (hxc.comp (continuous_const.sub continuous_id)).continuousAt
    exact ((Polynomial.continuous _).continuousAt.comp h1).mul
      ((ratFunc_eval_continuousAt _ hRD).comp (f := fun s : ℂ => x (1 - s)) h1)
  have hRtc : ContinuousAt Rt s₀ := by
    have h1 : ContinuousAt x s₀ := hxc.continuousAt
    have he : ContinuousAt (fun s => epsilonMonomial q (c₀ * c₁) (m₀ + m₁) s) s₀ := by
      unfold epsilonMonomial
      exact continuousAt_const.mul (h1.zpow₀ _ (Or.inl (spectralPoint_ne_zero_of_pos hq0 s₀)))
    exact (continuousAt_const.mul he).mul
      (((Polynomial.continuous _).continuousAt.comp h1).mul
        ((ratFunc_eval_continuousAt _ hR).comp h1))
  -- The finitely many real perturbations hitting a summand denominator.
  let bad : Set ℝ :=
    (⋃ j ∈ J, {t : ℝ | (R₀ j).denom.eval (x (s₀ + ((1 * t : ℝ) : ℂ))) = 0}) ∪
    (⋃ j ∈ J, {t : ℝ | (R₁ j).denom.eval (x (s₀ + ((1 * t : ℝ) : ℂ))) = 0}) ∪
    (⋃ j ∈ J, {t : ℝ | (RD₀ j).denom.eval (x ((1 - s₀) + ((-1 * t : ℝ) : ℂ))) = 0}) ∪
    (⋃ j ∈ J, {t : ℝ | (RD₁ j).denom.eval (x ((1 - s₀) + ((-1 * t : ℝ) : ℂ))) = 0})
  have hbad : bad.Finite := by
    refine (((?_ : Set.Finite _).union ?_).union ?_).union ?_ <;>
      refine J.finite_toSet.biUnion fun j _ => ?_
    · exact finite_ray_zeros hq s₀ 1 one_ne_zero (RatFunc.denom_ne_zero _)
    · exact finite_ray_zeros hq s₀ 1 one_ne_zero (RatFunc.denom_ne_zero _)
    · exact finite_ray_zeros hq (1 - s₀) (-1) (by norm_num) (RatFunc.denom_ne_zero _)
    · exact finite_ray_zeros hq (1 - s₀) (-1) (by norm_num) (RatFunc.denom_ne_zero _)
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), L (s₀ + (t : ℂ)) = Rt (s₀ + (t : ℂ)) := by
    filter_upwards [nhdsNE_le_cofinite (0 : ℝ) hbad.compl_mem_cofinite] with t ht
    simp only [bad, Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq,
      not_or, not_exists] at ht
    obtain ⟨⟨⟨hb₀, hb₁⟩, hb₂⟩, hb₃⟩ := ht
    have e1 : s₀ + ((1 * t : ℝ) : ℂ) = s₀ + (t : ℂ) := by push_cast; ring
    have e2 : (1 - s₀) + ((-1 * t : ℝ) : ℂ) = 1 - (s₀ + (t : ℂ)) := by push_cast; ring
    simp only [e1, e2] at hb₀ hb₁ hb₂ hb₃
    set s := s₀ + (t : ℂ)
    have hA₀ : ∀ j ∈ J, (R₀ j).denom.eval (x s) ≠ 0 := fun j hj => hb₀ j hj
    have hA₁ : ∀ j ∈ J, (R₁ j).denom.eval (x s) ≠ 0 := fun j hj => hb₁ j hj
    have hD₀ : ∀ j ∈ J, (RD₀ j).denom.eval (x (1 - s)) ≠ 0 := fun j hj => hb₂ j hj
    have hD₁ : ∀ j ∈ J, (RD₁ j).denom.eval (x (1 - s)) ≠ 0 := fun j hj => hb₃ j hj
    simp only [hL, hRt]
    rw [(ratFunc_sum_mul_eval J RD₀ RD₁ _ hD₀ hD₁).2,
      (ratFunc_sum_mul_eval J R₀ R₁ _ hA₀ hA₁).2, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have e₀ := h₀ j hj s (hA₀ j hj) (hD₀ j hj)
    have e₁ := h₁ j hj s (hA₁ j hj) (hD₁ j hj)
    simp only [Units.val_one, one_pow, one_mul, epsilonMonomial] at e₀ e₁ ⊢
    have hxs : x s ≠ 0 := spectralPoint_ne_zero_of_pos hq0 s
    calc (Pd₀ * Pd₁).eval (x (1 - s)) *
          (RatFunc.eval (RingHom.id ℂ) (x (1 - s)) (RD₀ j) *
            RatFunc.eval (RingHom.id ℂ) (x (1 - s)) (RD₁ j))
        = (Pd₀.eval (spectralPoint q (1 - s)) *
              RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) (RD₀ j)) *
            (Pd₁.eval (spectralPoint q (1 - s)) *
              RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) (RD₁ j)) := by
          rw [Polynomial.eval_mul]; ring
      _ = ((c₀ : ℂ) * spectralPoint q s ^ m₀ *
              (P₀.eval (spectralPoint q s) *
                RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) (R₀ j))) *
            ((c₁ : ℂ) * spectralPoint q s ^ m₁ *
              (P₁.eval (spectralPoint q s) *
                RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) (R₁ j))) := by
          rw [e₀, e₁]
      _ = ((c₀ * c₁ : ℂˣ) : ℂ) * x s ^ (m₀ + m₁) *
            ((P₀ * P₁).eval (x s) *
              (RatFunc.eval (RingHom.id ℂ) (x s) (R₀ j) *
                RatFunc.eval (RingHom.id ℂ) (x s) (R₁ j))) := by
          rw [Polynomial.eval_mul, zpow_add₀ hxs, Units.val_mul]; ring
  have hlim : Tendsto (fun t : ℝ => s₀ + (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 s₀) := by
    have h : Tendsto (fun t : ℝ => s₀ + (t : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (s₀ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simp only [Complex.ofReal_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq (hLc.tendsto.comp hlim) (hRtc.tendsto.comp hlim) hev

/-- If two functions agree on a right half-plane with finite sums of products of
functions whose factors satisfy two families of normalized functional
equations, then any rational continuations of the two functions satisfy the
combined equation, with product polynomials, product unit and summed exponent.
The two sums use the same finite index set. -/
theorem normalizedFunctionalEquation_of_eventually_sum_mul {q : ℕ} (hq : 1 < q) {ι : Type*}
    (J : Finset ι) {P₀ Pd₀ P₁ Pd₁ : Polynomial ℂ} {c₀ c₁ : ℂˣ} {m₀ m₁ : ℤ}
    {Z ZD : ℂ → ℂ} {R RD : RatFunc ℂ}
    (hR : HasRationalContinuation q Z R) (hRD : HasRationalContinuation q ZD RD)
    (z₀ z₁ zd₀ zd₁ : ι → ℂ → ℂ) (R₀ R₁ RD₀ RD₁ : ι → RatFunc ℂ)
    (hZ : ∃ b : ℝ, ∀ s : ℂ, b < s.re → Z s = ∑ j ∈ J, z₀ j s * z₁ j s)
    (hZD : ∃ b : ℝ, ∀ s : ℂ, b < s.re → ZD s = ∑ j ∈ J, zd₀ j s * zd₁ j s)
    (hR₀ : ∀ j ∈ J, HasRationalContinuation q (z₀ j) (R₀ j))
    (hR₁ : ∀ j ∈ J, HasRationalContinuation q (z₁ j) (R₁ j))
    (hRD₀ : ∀ j ∈ J, HasRationalContinuation q (zd₀ j) (RD₀ j))
    (hRD₁ : ∀ j ∈ J, HasRationalContinuation q (zd₁ j) (RD₁ j))
    (h₀ : ∀ j ∈ J, NormalizedFunctionalEquation q P₀ Pd₀ 1 c₀ 0 m₀ (R₀ j) (RD₀ j))
    (h₁ : ∀ j ∈ J, NormalizedFunctionalEquation q P₁ Pd₁ 1 c₁ 0 m₁ (R₁ j) (RD₁ j)) :
    NormalizedFunctionalEquation q (P₀ * P₁) (Pd₀ * Pd₁) 1 (c₀ * c₁) 0 (m₀ + m₁) R RD := by
  have e : R = ∑ j ∈ J, R₀ j * R₁ j :=
    hR.unique hq (RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_sum_mul J z₀ z₁ R₀ R₁ hR₀ hR₁) hZ)
  have eD : RD = ∑ j ∈ J, RD₀ j * RD₁ j :=
    hRD.unique hq (RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_sum_mul J zd₀ zd₁ RD₀ RD₁ hRD₀ hRD₁) hZD)
  rw [e, eD]
  exact normalizedFunctionalEquation_sum_mul hq J R₀ RD₀ R₁ RD₁ h₀ h₁

end FunctionalEquation

end Langlands.GodementJacquet
