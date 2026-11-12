import Langlands.Representation.GodementJacquet.LocalTateMellin

/-! # Laurent numerators of scalar Mellin integrals over a local field -/

noncomputable section

namespace Langlands.GodementJacquet.LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel Conductor RankinSelberg Polynomial
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : Normalization F)

/-- The Euler polynomial of a character with unit conductor `a`. -/
def eulerPoly (η : Fˣ →* ℂˣ) (a : ℕ) : ℂ[X] :=
  if a = 0 then 1 - C (η N.ϖ : ℂ) * X else 1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eulerPoly_coeff_zero (η : Fˣ →* ℂˣ) (a : ℕ) : (N.eulerPoly η a).coeff 0 = 1 := by
  unfold eulerPoly
  split_ifs <;> simp

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eulerPoly_ne_zero (η : Fˣ →* ℂˣ) (a : ℕ) : N.eulerPoly η a ≠ 0 := by
  intro h
  have := N.eulerPoly_coeff_zero η a
  rw [h, coeff_zero] at this
  exact zero_ne_one this

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eulerPoly_eval_ne_zero (η : Fˣ →* ℂˣ) (a : ℕ) {x : ℂ}
    (hx : ‖(η N.ϖ : ℂ) * x‖ < 1) : (N.eulerPoly η a).eval x ≠ 0 := by
  unfold eulerPoly
  split_ifs
  · simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    intro h
    have h1 : (η N.ϖ : ℂ) * x = 1 := by linear_combination -h
    rw [h1, norm_one] at hx
    exact lt_irrefl _ hx
  · simp

variable [MeasurableSpace Fˣ] [BorelSpace Fˣ]

/-- Laurent data of a Mellin integral: on a right half-plane the integrand is
integrable and `P(q ^ (-s)) Z(Φ, η, s)` is the evaluation of `ℓ` at `q ^ (-s)`. -/
def HasLaurentMellin (η : Fˣ →* ℂˣ) (P : ℂ[X]) (Φ : SchwartzBruhat F)
    (ℓ : LaurentCoefficients) : Prop :=
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    Integrable (scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s)
        (localMultiplicativeHaar F) ∧
      P.eval (spectralPoint N.q s) *
          scalarMellinIntegral N.abv (localMultiplicativeHaar F) (fun x => (η x : ℂ)) 1 Φ s =
        laurentEval (spectralUnit N.q_pos s) ℓ

/-- The explicit Laurent numerator of the shell expansion between the lattice
bounds `A ≤ M`. -/
def shellLaurent (η : Fˣ →* ℂˣ) (a : ℕ) (Φ : SchwartzBruhat F) (A M : ℤ) :
    LaurentCoefficients :=
  Polynomial.toLaurent (N.eulerPoly η a) *
      ∑ n ∈ Finset.range (M - A).toNat,
        LaurentPolynomial.C ((η N.ϖ : ℂ) ^ (A + n) * N.shellCoeff η Φ (A + n)) *
          LaurentPolynomial.T (A + n) +
    LaurentPolynomial.C (Φ 0 * (if a = 0 then 1 else 0) * (η N.ϖ : ℂ) ^ M) *
      LaurentPolynomial.T M

/-- **Shell expansion, Laurent form.** -/
theorem hasLaurentMellin_shellLaurent {η : Fˣ →* ℂˣ} (hηc : Continuous η) {a : ℕ}
    (hη : N.IsUnitConductor η a) (Φ : SchwartzBruhat F) {A M : ℤ} (hAM : A ≤ M)
    (hA : ∀ x, x ∉ N.ball A → Φ x = 0) (hM : ∀ x ∈ N.ball M, Φ x = Φ 0) :
    N.HasLaurentMellin η (N.eulerPoly η a) Φ (N.shellLaurent η a Φ A M) := by
  refine ⟨Real.logb N.q ‖(η N.ϖ : ℂ)‖, fun s hs => ?_⟩
  have hlt : ‖(η N.ϖ : ℂ) * spectralPoint N.q s‖ < 1 := N.norm_mul_spectralPoint_lt_one _ hs
  refine ⟨(N.mellin_hasSum η hηc Φ hA hlt).1, ?_⟩
  rw [N.mellin_eq hηc hη Φ hAM hA hM hlt, shellLaurent]
  simp only [map_add, map_mul, map_sum, laurentEval_toLaurent, laurentEval_C, laurentEval_T,
    coe_spectralUnit]
  set X := spectralPoint N.q s with hX
  have hX0 : X ≠ 0 := spectralPoint_ne_zero_of_pos N.q_pos s
  have hsum : ∑ n ∈ Finset.range (M - A).toNat,
      ((η N.ϖ : ℂ) * X) ^ (A + n) * N.shellCoeff η Φ (A + n) =
      ∑ n ∈ Finset.range (M - A).toNat,
        (η N.ϖ : ℂ) ^ (A + n) * N.shellCoeff η Φ (A + n) * X ^ (A + n) :=
    Finset.sum_congr rfl fun n _ => by rw [mul_zpow]; ring
  rw [mul_add, hsum]
  congr 1
  by_cases ha : a = 0
  · have h1 : 1 - (η N.ϖ : ℂ) * X ≠ 0 := by
      intro h
      have h2 : (η N.ϖ : ℂ) * X = 1 := by linear_combination -h
      rw [h2, norm_one] at hlt
      exact lt_irrefl _ hlt
    simp only [eulerPoly, ha, ↓reduceIte, eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_zpow]
    calc (1 - (η N.ϖ : ℂ) * X) * (Φ 0 * 1 * ((η N.ϖ : ℂ) ^ M * X ^ M) *
          (1 - (η N.ϖ : ℂ) * X)⁻¹) =
        ((1 - (η N.ϖ : ℂ) * X) * (1 - (η N.ϖ : ℂ) * X)⁻¹) *
          (Φ 0 * 1 * (η N.ϖ : ℂ) ^ M * X ^ M) := by ring
      _ = Φ 0 * 1 * (η N.ϖ : ℂ) ^ M * X ^ M := by rw [mul_inv_cancel₀ h1, one_mul]
  · simp [eulerPoly, ha]

theorem hasLaurentMellin_zero (η : Fˣ →* ℂˣ) (P : ℂ[X]) :
    N.HasLaurentMellin η P 0 0 := by
  refine ⟨0, fun s _ => ?_⟩
  have h0 : scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 (0 : SchwartzBruhat F) s = 0 := by
    funext x
    simp only [scalarMellinIntegrand, Pi.zero_apply]
    change (0 : ℂ) * _ * _ = 0
    ring
  refine ⟨by rw [h0]; exact integrable_zero _ _ _, ?_⟩
  rw [scalarMellinIntegral, h0]
  simp only [Pi.zero_apply, integral_zero, mul_zero, map_zero]

theorem hasLaurentMellin_add {η : Fˣ →* ℂˣ} {P : ℂ[X]} {Φ Ψ : SchwartzBruhat F}
    {ℓ ℓ' : LaurentCoefficients} (h : N.HasLaurentMellin η P Φ ℓ)
    (h' : N.HasLaurentMellin η P Ψ ℓ') : N.HasLaurentMellin η P (Φ + Ψ) (ℓ + ℓ') := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨σ', hσ'⟩ := h'
  refine ⟨max σ σ', fun s hs => ?_⟩
  obtain ⟨hi, he⟩ := hσ s ((le_max_left _ _).trans_lt hs)
  obtain ⟨hi', he'⟩ := hσ' s ((le_max_right _ _).trans_lt hs)
  have hfun : scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 (Φ + Ψ) s =
      scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s +
        scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Ψ s := by
    funext x
    simp only [scalarMellinIntegrand, Pi.add_apply]
    change (Φ (x : F) + Ψ (x : F)) * _ * _ = _
    ring
  refine ⟨by rw [hfun]; exact hi.add hi', ?_⟩
  rw [scalarMellinIntegral, hfun]
  simp only [Pi.add_apply]
  rw [integral_add hi hi', mul_add, map_add, ← he, ← he']
  rfl

theorem hasLaurentMellin_smul {η : Fˣ →* ℂˣ} {P : ℂ[X]} {Φ : SchwartzBruhat F}
    {ℓ : LaurentCoefficients} (h : N.HasLaurentMellin η P Φ ℓ) (c : ℂ) :
    N.HasLaurentMellin η P (c • Φ) (c • ℓ) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨hi, he⟩ := hσ s hs
  have hfun : scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 (c • Φ) s =
      fun x => c * scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s x := by
    funext x
    simp only [scalarMellinIntegrand]
    change (c * Φ (x : F)) * _ * _ = _
    ring
  refine ⟨by rw [hfun]; exact hi.const_mul c, ?_⟩
  rw [scalarMellinIntegral, hfun, integral_const_mul, laurentEval_smul, ← he]
  rw [scalarMellinIntegral]
  ring

theorem hasLaurentMellin_dilate {η : Fˣ →* ℂˣ} {P : ℂ[X]} {Φ : SchwartzBruhat F}
    {ℓ : LaurentCoefficients} (h : N.HasLaurentMellin η P Φ ℓ) (b : Fˣ) :
    N.HasLaurentMellin η P (Normalization.dilate b Φ)
      (LaurentPolynomial.C ((η b : ℂ)⁻¹) * LaurentPolynomial.T (-N.ord (b : F)) * ℓ) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨hi, he⟩ := hσ s hs
  set f := scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s with hf
  set X := spectralPoint N.q s with hX
  have hX0 : X ≠ 0 := spectralPoint_ne_zero_of_pos N.q_pos s
  have hb0 : (η b : ℂ) ≠ 0 := (η b).ne_zero
  set c : ℂ := (η b : ℂ)⁻¹ * X ^ (-N.ord (b : F)) with hc
  have key : scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 (Normalization.dilate b Φ) s =
      fun x => c * f (b * x) := by
    funext x
    simp only [hf, scalarMellinIntegrand, dilate_apply, Units.val_mul, map_mul]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (N.abv.nonneg _) (N.abv.nonneg _),
      N.abv_eq b.ne_zero, natCast_zpow_cpow_eq N.q N.q_pos, hc, zpow_neg]
    have e1 : (η b : ℂ)⁻¹ * (η b : ℂ) = 1 := inv_mul_cancel₀ hb0
    have e2 : (X ^ N.ord (b : F))⁻¹ * X ^ N.ord (b : F) = 1 :=
      inv_mul_cancel₀ (zpow_ne_zero _ hX0)
    linear_combination
      (-(Φ ((b : F) * x) * (η x : ℂ) * ((N.abv (x : F) : ℂ)) ^ (((1 : ℕ) : ℂ) * s)) *
        ((X ^ N.ord (b : F))⁻¹ * X ^ N.ord (b : F))) * e1 +
      (-(Φ ((b : F) * x) * (η x : ℂ) * ((N.abv (x : F) : ℂ)) ^ (((1 : ℕ) : ℂ) * s))) * e2
  refine ⟨by rw [key]; exact (hi.comp_mul_left b).const_mul c, ?_⟩
  rw [scalarMellinIntegral, key, integral_const_mul,
    integral_mul_left_eq_self (μ := localMultiplicativeHaar F) f b]
  simp only [map_mul, laurentEval_C, laurentEval_T, coe_spectralUnit]
  rw [← he, scalarMellinIntegral, hc]
  ring

/-- Every Schwartz--Bruhat function has Laurent data with the Euler polynomial. -/
theorem exists_hasLaurentMellin {η : Fˣ →* ℂˣ} (hηc : Continuous η) {a : ℕ}
    (hη : N.IsUnitConductor η a) (Φ : SchwartzBruhat F) :
    ∃ ℓ, N.HasLaurentMellin η (N.eulerPoly η a) Φ ℓ := by
  obtain ⟨A, M, hAM, hA, hM⟩ := N.exists_support_bounds Φ
  exact ⟨_, N.hasLaurentMellin_shellLaurent hηc hη Φ hAM hA hM⟩

/-- One half-plane of absolute convergence for all Schwartz--Bruhat functions. -/
theorem integrable_mellinIntegrand {η : Fˣ →* ℂˣ} (hηc : Continuous η) (Φ : SchwartzBruhat F)
    {s : ℂ} (hs : Real.logb N.q ‖(η N.ϖ : ℂ)‖ < s.re) :
    Integrable (scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s)
      (localMultiplicativeHaar F) := by
  obtain ⟨A, M, hAM, hA, hM⟩ := N.exists_support_bounds Φ
  exact (N.mellin_hasSum η hηc Φ hA (N.norm_mul_spectralPoint_lt_one _ hs)).1

/-- Laurent data give the rational continuation `ℓ / P`. -/
theorem hasRationalContinuation_of_hasLaurentMellin {η : Fˣ →* ℂˣ} {a : ℕ}
    {Φ : SchwartzBruhat F} {ℓ : LaurentCoefficients}
    (h : N.HasLaurentMellin η (N.eulerPoly η a) Φ ℓ) :
    HasRationalContinuation N.q
      (scalarMellinIntegral N.abv (localMultiplicativeHaar F) (fun x => (η x : ℂ)) 1 Φ)
      (laurentToRatFunc ℓ / algebraMap ℂ[X] RationalFunctions (N.eulerPoly η a)) := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow ℓ
  have hrepr : laurentToRatFunc ℓ / algebraMap ℂ[X] RationalFunctions (N.eulerPoly η a) =
      algebraMap ℂ[X] RationalFunctions p /
        algebraMap ℂ[X] RationalFunctions (X ^ n * N.eulerPoly η a) := by
    have hTn : laurentToRatFunc (LaurentPolynomial.T (n : ℤ)) =
        algebraMap ℂ[X] RationalFunctions (X ^ n) := by
      rw [laurentToRatFunc_T, zpow_natCast, map_pow, RatFunc.algebraMap_X]
    have hXn : algebraMap ℂ[X] RationalFunctions (X ^ n) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (pow_ne_zero _ X_ne_zero)
    have h1 : algebraMap ℂ[X] RationalFunctions p =
        laurentToRatFunc ℓ * algebraMap ℂ[X] RationalFunctions (X ^ n) := by
      rw [← laurentToRatFunc_toLaurent, hp, map_mul, hTn]
    rw [h1, map_mul, mul_comm (algebraMap _ _ (X ^ n)), mul_div_mul_right _ _ hXn]
  refine ⟨max σ (Real.logb N.q ‖(η N.ϖ : ℂ)‖), fun s hs => ?_⟩
  obtain ⟨_, he⟩ := hσ s ((le_max_left _ _).trans_lt hs)
  have hlt : ‖(η N.ϖ : ℂ) * spectralPoint N.q s‖ < 1 :=
    N.norm_mul_spectralPoint_lt_one _ ((le_max_right _ _).trans_lt hs)
  have hP := N.eulerPoly_eval_ne_zero η a hlt
  have hX0 : spectralPoint N.q s ≠ 0 := spectralPoint_ne_zero_of_pos N.q_pos s
  have hD : (X ^ n * N.eulerPoly η a).eval (spectralPoint N.q s) ≠ 0 := by
    rw [eval_mul, eval_pow, eval_X]
    exact mul_ne_zero (pow_ne_zero _ hX0) hP
  obtain ⟨hreg, heval⟩ := regular_and_eval_div (spectralPoint N.q s) p _ hD
  rw [hrepr]
  refine ⟨hreg, ?_⟩
  rw [heval]
  have hpe : p.eval (spectralPoint N.q s) =
      laurentEval (spectralUnit N.q_pos s) ℓ * spectralPoint N.q s ^ n := by
    rw [← coe_spectralUnit N.q_pos s, ← laurentEval_toLaurent, hp, map_mul, laurentEval_T,
      zpow_natCast]
  rw [hpe, ← he, eval_mul, eval_pow, eval_X,
    eq_div_iff (mul_ne_zero (pow_ne_zero _ hX0) hP)]
  ring

/-- Any rational continuation of a Mellin integral with Laurent data is `ℓ / P`. -/
theorem laurentToRatFunc_eq_of_hasLaurentMellin {η : Fˣ →* ℂˣ} {a : ℕ}
    {Φ : SchwartzBruhat F} {ℓ : LaurentCoefficients}
    (h : N.HasLaurentMellin η (N.eulerPoly η a) Φ ℓ) {R : RationalFunctions}
    (hR : HasRationalContinuation N.q
      (scalarMellinIntegral N.abv (localMultiplicativeHaar F) (fun x => (η x : ℂ)) 1 Φ) R) :
    laurentToRatFunc ℓ = algebraMap ℂ[X] RationalFunctions (N.eulerPoly η a) * R := by
  rw [hR.unique N.one_lt_q (N.hasRationalContinuation_of_hasLaurentMellin h), mul_div_cancel₀]
  exact RatFunc.algebraMap_ne_zero (N.eulerPoly_ne_zero η a)

end Normalization

end Langlands.GodementJacquet.LocalTate
