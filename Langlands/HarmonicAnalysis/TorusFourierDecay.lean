import Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Group.Integral

/-! # Rapid decay of Fourier coefficients of smooth functions on a finite product of circles

For a smooth function `f` on the torus `T = J → Circle` (`J` finite) and a finite invariant
measure `μ` on `T`, the Fourier coefficient `∫ f(z) ∏ⱼ zⱼ^{nⱼ} dμ(z)` at `n : J → ℤ` is bounded
by `(1 + ‖n‖)^{-k}` times the supremum of `|f|` and of the `k`-th partial derivatives
`|∂ⱼ^k f|`. This is estimate (4) of the proof of Proposition VI.3.1 in Waldspurger's
*La formule de Plancherel pour les groupes p-adiques*, for a torus written in coordinates.

The proof differentiates the translation identity `∫ f(z eᶿ) χₙ(z) dμ = χₙ(eᶿ)⁻¹ ∫ f χₙ dμ` at
`θ = 0`, which gives `∫ ∂ⱼf · χₙ dμ = -i nⱼ ∫ f χₙ dμ`.
-/

noncomputable section

open MeasureTheory Complex
open Langlands.Plancherel
open scoped ContDiff

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J : Type*} [Fintype J]

/-- The character `z ↦ ∏ⱼ zⱼ^{nⱼ}` of the torus `J → Circle` attached to `n : J → ℤ`. -/
def torusCharacter (n : J → ℤ) (z : J → Circle) : ℂ :=
  ∏ j, ((z j ^ n j : Circle) : ℂ)

/-- The partial derivative of `f : (J → Circle) → ℂ` in the `j`-th angle: the derivative at
`θ = 0` of `θ ↦ f(z · e^{iθ}_j)`, where `e^{iθ}_j` is `e^{iθ}` in coordinate `j` and `1`
elsewhere. -/
def torusPartialDeriv [DecidableEq J] (j : J) (f : (J → Circle) → ℂ) (z : J → Circle) : ℂ :=
  deriv (fun θ : ℝ => f (z * finiteTorusExp (Pi.single j θ))) 0

/-- The Fourier coefficient `∫ f(z) χₙ(z) dμ(z)` of `f` at `n : J → ℤ`. -/
def torusFourierCoeff (μ : Measure (J → Circle)) (f : (J → Circle) → ℂ) (n : J → ℤ) : ℂ :=
  ∫ z, f z * torusCharacter n z ∂μ

theorem torusCharacter_mul (n : J → ℤ) (z w : J → Circle) :
    torusCharacter n (z * w) = torusCharacter n z * torusCharacter n w := by
  simp only [torusCharacter, Pi.mul_apply, mul_zpow, Circle.coe_mul, Finset.prod_mul_distrib]

theorem norm_torusCharacter (n : J → ℤ) (z : J → Circle) : ‖torusCharacter n z‖ = 1 := by
  simp [torusCharacter]

theorem continuous_torusCharacter (n : J → ℤ) : Continuous (torusCharacter n) := by
  unfold torusCharacter
  exact continuous_finsetProd _ fun j _ =>
    continuous_subtype_val.comp ((continuous_apply j).zpow (n j))

omit [Fintype J] in
theorem finiteTorusExp_zero : finiteTorusExp (0 : J → ℝ) = 1 := by
  funext i
  simp [finiteTorusExp, Circle.exp_zero]

theorem torusCharacter_finiteTorusExp_single [DecidableEq J] (n : J → ℤ) (j : J) (θ : ℝ) :
    torusCharacter n (finiteTorusExp (Pi.single j θ)) = Complex.exp (((n j : ℝ) * θ : ℝ) * I) := by
  rw [torusCharacter, Finset.prod_eq_single j]
  · simp [finiteTorusExp, ← Circle.exp_intCast_mul, Circle.coe_exp]
  · intro i _ hij
    simp [finiteTorusExp, hij, Circle.exp_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

section Derivative

variable [DecidableEq J]

/-- Derivative along the `j`-th angle of the lift `F = f ∘ exp` of a smooth torus function. -/
theorem hasDerivAt_comp_finiteTorusExp {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (x : J → ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => f (finiteTorusExp x * finiteTorusExp (Pi.single j t)))
      (fderiv ℝ (f ∘ finiteTorusExp) (x + Pi.single j θ) (Pi.single j 1)) θ := by
  have hF : Differentiable ℝ (f ∘ finiteTorusExp) := hf.differentiable (by simp)
  have hL : HasDerivAt (fun t : ℝ => x + Pi.single j t) (Pi.single j 1) θ := by
    have := (ContinuousLinearMap.single ℝ (fun _ : J => ℝ) j).hasFDerivAt (x := θ)
    have h2 := this.hasDerivAt.const_add x
    simpa using h2
  have := (hF (x + Pi.single j θ)).hasFDerivAt.comp_hasDerivAt θ hL
  simpa only [Function.comp_def, finiteTorusExp_add] using this

theorem torusPartialDeriv_finiteTorusExp {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (x : J → ℝ) :
    torusPartialDeriv j f (finiteTorusExp x) =
      fderiv ℝ (f ∘ finiteTorusExp) x (Pi.single j 1) := by
  have := (hasDerivAt_comp_finiteTorusExp hf j x 0).deriv
  simpa [torusPartialDeriv] using this

/-- Translation along the `j`-th angle has derivative `∂ⱼ f` at every point. -/
theorem hasDerivAt_torusTranslate {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (z : J → Circle) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => f (z * finiteTorusExp (Pi.single j t)))
      (torusPartialDeriv j f (z * finiteTorusExp (Pi.single j θ))) θ := by
  obtain ⟨x, rfl⟩ := (isOpenQuotientMap_finiteTorusExp J).surjective z
  rw [← finiteTorusExp_add, torusPartialDeriv_finiteTorusExp hf]
  exact hasDerivAt_comp_finiteTorusExp hf j x θ

theorem isSmoothFiniteTorusFunction_torusPartialDeriv {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) :
    IsSmoothFiniteTorusFunction (torusPartialDeriv j f) := by
  have hfun : torusPartialDeriv j f ∘ finiteTorusExp =
      fun x => fderiv ℝ (f ∘ finiteTorusExp) x (Pi.single j 1) := by
    funext x
    exact torusPartialDeriv_finiteTorusExp hf j x
  unfold IsSmoothFiniteTorusFunction
  rw [hfun]
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem isSmoothFiniteTorusFunction_iterate_torusPartialDeriv {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (k : ℕ) :
    IsSmoothFiniteTorusFunction ((torusPartialDeriv j)^[k] f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact isSmoothFiniteTorusFunction_torusPartialDeriv ih j

end Derivative

section Coefficients

variable [DecidableEq J] (μ : Measure (J → Circle)) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]

omit [DecidableEq J] in
theorem exists_norm_le_of_isSmooth {f : (J → Circle) → ℂ} (hf : IsSmoothFiniteTorusFunction f) :
    ∃ C, ∀ z, ‖f z‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuous.continuousOn
  exact ⟨C, fun z => hC z (Set.mem_univ z)⟩

omit [IsFiniteMeasure μ] in
/-- Translating the argument of `f` by `e^{iθ}_j` multiplies its Fourier coefficient at `n`
by `e^{-i nⱼ θ}`. -/
theorem integral_translate_mul_torusCharacter (f : (J → Circle) → ℂ) (n : J → ℤ) (j : J)
    (θ : ℝ) :
    ∫ z, f (z * finiteTorusExp (Pi.single j θ)) * torusCharacter n z ∂μ =
      torusFourierCoeff μ f n * Complex.exp (((n j : ℝ) * (-θ) : ℝ) * I) := by
  set e := finiteTorusExp (Pi.single j θ)
  have he : e * finiteTorusExp (Pi.single j (-θ)) = 1 := by
    rw [← finiteTorusExp_add, ← Pi.single_add, add_neg_cancel, Pi.single_zero,
      finiteTorusExp_zero]
  have hpt : ∀ z, f (z * e) * torusCharacter n z =
      (f (z * e) * torusCharacter n (z * e)) *
        torusCharacter n (finiteTorusExp (Pi.single j (-θ))) := by
    intro z
    rw [mul_assoc, ← torusCharacter_mul, mul_assoc, he, mul_one]
  simp_rw [hpt]
  rw [integral_mul_const, integral_mul_right_eq_self (fun z => f z * torusCharacter n z) e,
    torusCharacter_finiteTorusExp_single]
  rfl

/-- **Integration by parts on the torus**: `∫ ∂ⱼf · χₙ dμ = -i nⱼ ∫ f χₙ dμ`. -/
theorem torusFourierCoeff_torusPartialDeriv {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (n : J → ℤ) :
    torusFourierCoeff μ (torusPartialDeriv j f) n =
      -((n j : ℂ) * I) * torusFourierCoeff μ f n := by
  have hf' := isSmoothFiniteTorusFunction_torusPartialDeriv hf j
  obtain ⟨C, hC⟩ := exists_norm_le_of_isSmooth hf'
  set F : ℝ → (J → Circle) → ℂ := fun θ z =>
    f (z * finiteTorusExp (Pi.single j θ)) * torusCharacter n z with hFdef
  set F' : ℝ → (J → Circle) → ℂ := fun θ z =>
    torusPartialDeriv j f (z * finiteTorusExp (Pi.single j θ)) * torusCharacter n z with hF'def
  have hcontF : ∀ θ, Continuous (F θ) := fun θ =>
    (hf.continuous.comp (continuous_id.mul continuous_const)).mul (continuous_torusCharacter n)
  have hcontF' : ∀ θ, Continuous (F' θ) := fun θ =>
    (hf'.continuous.comp (continuous_id.mul continuous_const)).mul (continuous_torusCharacter n)
  obtain ⟨C0, hC0⟩ := exists_norm_le_of_isSmooth hf
  have hint0 : Integrable (F 0) μ := by
    refine Integrable.of_bound (hcontF 0).aestronglyMeasurable C0 (Filter.Eventually.of_forall ?_)
    intro z
    simp only [hFdef, norm_mul, norm_torusCharacter, mul_one]
    exact hC0 _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ => C) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ => (hcontF θ).aestronglyMeasurable) hint0
    (F' := F') (hcontF' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z θ _ => by
      simp only [hF'def, norm_mul, norm_torusCharacter, mul_one]
      exact hC _)
    (integrable_const C)
    (Filter.Eventually.of_forall fun z θ _ =>
      (hasDerivAt_torusTranslate hf j z θ).mul_const (torusCharacter n z))
  have hΦ : (fun θ => ∫ z, F θ z ∂μ) =
      fun θ : ℝ => torusFourierCoeff μ f n * Complex.exp (((n j : ℝ) * (-θ) : ℝ) * I) := by
    funext θ
    exact integral_translate_mul_torusCharacter μ f n j θ
  have hexp : HasDerivAt
      (fun θ : ℝ => torusFourierCoeff μ f n * Complex.exp (((n j : ℝ) * (-θ) : ℝ) * I))
      (torusFourierCoeff μ f n * (Complex.exp ((((n j : ℝ) * (-0 : ℝ)) : ℝ) * I) *
        ((-(n j : ℝ) : ℝ) * I))) 0 := by
    have h1 : HasDerivAt (fun θ : ℝ => (((n j : ℝ) * (-θ) : ℝ) : ℂ)) ((-(n j : ℝ) : ℝ) : ℂ) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).neg.const_mul (n j : ℝ)).ofReal_comp
      simpa using this
    exact ((h1.mul_const I).cexp).const_mul _
  rw [hΦ] at key
  have huniq := key.2.unique hexp
  have h0 : ∫ z, F' 0 z ∂μ = torusFourierCoeff μ (torusPartialDeriv j f) n := by
    simp [hF'def, torusFourierCoeff, Pi.single_zero, finiteTorusExp_zero]
  rw [← h0, huniq]
  simp
  ring

theorem torusFourierCoeff_iterate_torusPartialDeriv {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (n : J → ℤ) (k : ℕ) :
    torusFourierCoeff μ ((torusPartialDeriv j)^[k] f) n =
      (-((n j : ℂ) * I)) ^ k * torusFourierCoeff μ f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      torusFourierCoeff_torusPartialDeriv μ
        (isSmoothFiniteTorusFunction_iterate_torusPartialDeriv hf j k) j n, ih, pow_succ]
    ring

omit [DecidableEq J] [μ.IsMulLeftInvariant] in
theorem norm_torusFourierCoeff_le {f : (J → Circle) → ℂ} {M : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (n : J → ℤ) :
    ‖torusFourierCoeff μ f n‖ ≤ M * μ.real Set.univ := by
  unfold torusFourierCoeff
  refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, norm_torusCharacter, mul_one]
  exact hM z

/-- `|nⱼ|^k |f̂(n)| ≤ sup |∂ⱼ^k f| · μ(T)`. -/
theorem abs_pow_mul_norm_torusFourierCoeff_le {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (j : J) (k : ℕ) {M : ℝ}
    (hM : ∀ z, ‖(torusPartialDeriv j)^[k] f z‖ ≤ M) (n : J → ℤ) :
    |(n j : ℝ)| ^ k * ‖torusFourierCoeff μ f n‖ ≤ M * μ.real Set.univ := by
  have h := norm_torusFourierCoeff_le μ hM n
  rw [torusFourierCoeff_iterate_torusPartialDeriv μ hf j n k, norm_mul, norm_pow] at h
  have : ‖-((n j : ℂ) * I)‖ = |(n j : ℝ)| := by
    simp [Complex.norm_intCast]
  rwa [this] at h

end Coefficients

/-- `(1 + ‖n‖)^k ≤ 2^k (1 + ∑ⱼ |nⱼ|^k)` for the sup norm on `J → ℤ`. -/
theorem one_add_norm_pow_le (n : J → ℤ) (k : ℕ) :
    (1 + ‖n‖) ^ k ≤ 2 ^ k * (1 + ∑ j, |(n j : ℝ)| ^ k) := by
  have hsum : 0 ≤ ∑ j, |(n j : ℝ)| ^ k := Finset.sum_nonneg fun j _ => by positivity
  rcases le_or_gt ‖n‖ 1 with h | h
  · calc (1 + ‖n‖) ^ k ≤ 2 ^ k := by
          apply pow_le_pow_left₀ (by positivity); linarith
      _ ≤ 2 ^ k * (1 + ∑ j, |(n j : ℝ)| ^ k) := by
          have : (0 : ℝ) ≤ 2 ^ k := by positivity
          nlinarith
  · -- the sup norm is attained at some coordinate
    have hne : Nonempty J := by
      by_contra hJ
      rw [not_nonempty_iff] at hJ
      have : ‖n‖ = 0 := by simp [Subsingleton.elim n 0]
      linarith
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset J) Finset.univ_nonempty
      (fun j => ‖n j‖₊)
    have hnorm : ‖n‖ = |(n j : ℝ)| := by
      rw [Pi.norm_def, hj]
      simp [Int.norm_eq_abs]
    calc (1 + ‖n‖) ^ k ≤ (2 * ‖n‖) ^ k := by
          apply pow_le_pow_left₀ (by positivity); linarith
      _ = 2 ^ k * |(n j : ℝ)| ^ k := by rw [mul_pow, hnorm]
      _ ≤ 2 ^ k * (1 + ∑ j, |(n j : ℝ)| ^ k) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := Finset.single_le_sum (f := fun i => |(n i : ℝ)| ^ k)
            (fun i _ => by positivity) (Finset.mem_univ j)
          linarith

section Decay

variable [DecidableEq J] (μ : Measure (J → Circle)) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]

/-- **Rapid decay of Fourier coefficients** (Waldspurger, proof of Prop. VI.3.1, estimate (4),
in torus coordinates): if `|f| ≤ M` and `|∂ⱼ^k f| ≤ M` for every `j`, then
`(1 + ‖n‖)^k |f̂(n)| ≤ 2^k (1 + |J|) M μ(T)`. -/
theorem one_add_norm_pow_mul_norm_torusFourierCoeff_le {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) (k : ℕ) {M : ℝ} (hM0 : ∀ z, ‖f z‖ ≤ M)
    (hM : ∀ j z, ‖(torusPartialDeriv j)^[k] f z‖ ≤ M) (n : J → ℤ) :
    (1 + ‖n‖) ^ k * ‖torusFourierCoeff μ f n‖ ≤
      2 ^ k * (1 + Fintype.card J) * (M * μ.real Set.univ) := by
  have hc0 := norm_torusFourierCoeff_le μ hM0 n
  have hcj := fun j => abs_pow_mul_norm_torusFourierCoeff_le μ hf j k (hM j) n
  have hc : 0 ≤ ‖torusFourierCoeff μ f n‖ := norm_nonneg _
  calc (1 + ‖n‖) ^ k * ‖torusFourierCoeff μ f n‖
      ≤ 2 ^ k * (1 + ∑ j, |(n j : ℝ)| ^ k) * ‖torusFourierCoeff μ f n‖ :=
        mul_le_mul_of_nonneg_right (one_add_norm_pow_le n k) hc
    _ = 2 ^ k * (‖torusFourierCoeff μ f n‖ +
          ∑ j, |(n j : ℝ)| ^ k * ‖torusFourierCoeff μ f n‖) := by
        rw [mul_assoc, add_mul, one_mul, Finset.sum_mul]
    _ ≤ 2 ^ k * (M * μ.real Set.univ + ∑ _j : J, M * μ.real Set.univ) :=
        mul_le_mul_of_nonneg_left (add_le_add hc0 (Finset.sum_le_sum fun j _ => hcj j))
          (by positivity)
    _ = 2 ^ k * (1 + Fintype.card J) * (M * μ.real Set.univ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Estimate (4) with a real exponent: for `r ≤ k`,
`|f̂(n)| ≤ 2^k (1 + |J|) M μ(T) (1 + ‖n‖)^{-r}`. -/
theorem norm_torusFourierCoeff_le_rpow {f : (J → Circle) → ℂ}
    (hf : IsSmoothFiniteTorusFunction f) {k : ℕ} {r : ℝ} (hr : r ≤ k) {M : ℝ}
    (hM0 : ∀ z, ‖f z‖ ≤ M) (hM : ∀ j z, ‖(torusPartialDeriv j)^[k] f z‖ ≤ M) (n : J → ℤ) :
    ‖torusFourierCoeff μ f n‖ ≤
      2 ^ k * (1 + Fintype.card J) * (M * μ.real Set.univ) * (1 + ‖n‖) ^ (-r) := by
  have h := one_add_norm_pow_mul_norm_torusFourierCoeff_le μ hf k hM0 hM n
  have hpos : 0 < 1 + ‖n‖ := by positivity
  have hone : 1 ≤ 1 + ‖n‖ := by linarith [norm_nonneg n]
  have hkr : (1 + ‖n‖) ^ (-r) * (1 + ‖n‖) ^ k ≥ 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
    exact Real.one_le_rpow hone (by linarith)
  have hc : 0 ≤ ‖torusFourierCoeff μ f n‖ := norm_nonneg _
  have hrp : 0 ≤ (1 + ‖n‖) ^ (-r) := by positivity
  calc ‖torusFourierCoeff μ f n‖
      ≤ ‖torusFourierCoeff μ f n‖ * ((1 + ‖n‖) ^ (-r) * (1 + ‖n‖) ^ k) := by
        nlinarith
    _ = (1 + ‖n‖) ^ (-r) * ((1 + ‖n‖) ^ k * ‖torusFourierCoeff μ f n‖) := by ring
    _ ≤ (1 + ‖n‖) ^ (-r) * (2 ^ k * (1 + Fintype.card J) * (M * μ.real Set.univ)) :=
        mul_le_mul_of_nonneg_left h hrp
    _ = _ := by ring

end Decay

end Langlands.HarmonicAnalysis.TorusFourier
