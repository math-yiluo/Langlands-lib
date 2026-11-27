import Langlands.Analysis.OneParameterExponential
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Exponential polynomials in finite-dimensional translation-invariant function spaces -/

noncomputable section

open NormedSpace

set_option autoImplicit false

namespace Langlands.Global

section Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The polynomial function spaces increase with the degree bound. -/
theorem polynomialFunctions_mono {m n : ℕ} (h : m ≤ n) :
    polynomialFunctions V m ≤ polynomialFunctions V n := by
  apply Submodule.span_mono
  rintro _ ⟨k, hk, forms, rfl⟩
  exact ⟨k, hk.trans h, forms, rfl⟩

/-- Constant functions are polynomials of degree zero. -/
theorem const_mem_polynomialFunctions (c : ℂ) (n : ℕ) :
    (fun _ : V => c) ∈ polynomialFunctions V n := by
  have h1 : (fun _ : V => (1 : ℂ)) ∈ polynomialFunctions V n := by
    apply Submodule.subset_span
    refine ⟨0, Nat.zero_le n, Fin.elim0, ?_⟩
    funext v
    simp
  have h := (polynomialFunctions V n).smul_mem c h1
  convert h using 1
  funext v
  simp

/-- Multiplying a polynomial of degree at most `n` by a real-linear form gives a polynomial of
degree at most `n + 1`. -/
theorem linear_mul_mem_polynomialFunctions (ℓ : V →ₗ[ℝ] ℝ) {n : ℕ} {f : V → ℂ}
    (hf : f ∈ polynomialFunctions V n) :
    (fun v => ((ℓ v : ℝ) : ℂ) * f v) ∈ polynomialFunctions V (n + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, forms, rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨k + 1, Nat.succ_le_succ hk, Fin.cons ℓ forms, ?_⟩
    funext v
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  | zero =>
    convert (polynomialFunctions V (n + 1)).zero_mem using 1
    funext v
    simp
  | add f g _ _ hf hg =>
    convert (polynomialFunctions V (n + 1)).add_mem hf hg using 1
    funext v
    simp only [Pi.add_apply, mul_add]
  | smul c f _ hf =>
    convert (polynomialFunctions V (n + 1)).smul_mem c hf using 1
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Composition with a real-linear map preserves the polynomial function spaces. -/
theorem comp_linearMap_mem_polynomialFunctions {V' : Type*} [AddCommGroup V'] [Module ℝ V']
    (L : V' →ₗ[ℝ] V) {n : ℕ} {f : V → ℂ} (hf : f ∈ polynomialFunctions V n) :
    (f ∘ L) ∈ polynomialFunctions V' n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, forms, rfl⟩ := hf
    exact Submodule.subset_span ⟨k, hk, fun j => forms j ∘ₗ L, rfl⟩
  | zero => exact (polynomialFunctions V' n).zero_mem
  | add f g _ _ hf hg => exact (polynomialFunctions V' n).add_mem hf hg
  | smul c f _ hf => exact (polynomialFunctions V' n).smul_mem c hf

end Polynomial

section Nilpotent

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For endomorphisms `Y i`, the values of a linear form on the iterates
`(∑ i, t i • Y i) ^ k y` are polynomial functions of `t` of degree at most `k`. -/
theorem linearForm_pow_sum_smul_mem_polynomialFunctions (Y : ι → E →L[ℂ] E)
    (ℓ : E →ₗ[ℂ] ℂ) (k : ℕ) (y : E) :
    (fun t : ι → ℝ => ℓ (((∑ i, (t i : ℂ) • Y i) ^ k) y)) ∈
      polynomialFunctions (ι → ℝ) k := by
  induction k generalizing y with
  | zero =>
    simpa only [pow_zero, _root_.one_apply_eq_self] using
      const_mem_polynomialFunctions (V := ι → ℝ) (ℓ y) 0
  | succ k ih =>
    have heq : (fun t : ι → ℝ => ℓ (((∑ i, (t i : ℂ) • Y i) ^ (k + 1)) y)) =
        ∑ i, fun t : ι → ℝ => (((LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) t : ℝ) : ℂ) *
          ℓ (((∑ j, (t j : ℂ) • Y j) ^ k) (Y i y)) := by
      funext t
      have hpow : ((∑ i, (t i : ℂ) • Y i) ^ (k + 1)) y =
          ((∑ i, (t i : ℂ) • Y i) ^ k) ((∑ i, (t i : ℂ) • Y i) y) := by
        rw [pow_succ]
        rfl
      rw [hpow, _root_.sum_apply, map_sum, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [_root_.smul_apply, map_smul, map_smul, smul_eq_mul]
      rfl
    rw [heq]
    exact Submodule.sum_mem _ fun i _ =>
      linear_mul_mem_polynomialFunctions (LinearMap.proj i) (ih (Y i y))

end Nilpotent

section Decomposition

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exponential polynomials in a finite-dimensional translation-invariant space.** Let `T` be
an action of `ℝ^ι` by linear operators on functions `X → ℂ`, preserving a finite-dimensional
subspace `W` on which the orbit maps `t ↦ (T t w)(g)` are continuous. Then there is `n` such that
every `w ∈ W` is a finite sum of elements `u μ ∈ W` (`μ ∈ ℂ^ι`) for which
`t ↦ (T t (u μ))(g) · exp (-∑ i, t i μ i)` is a polynomial of degree at most `n`, for every
`g`. -/
theorem exists_exponentPolynomial_decomposition
    (T : Multiplicative (ι → ℝ) →* Module.End ℂ (X → ℂ))
    (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ t, ∀ w ∈ W, T t w ∈ W)
    (hcont : ∀ w ∈ W, ∀ g, Continuous fun t : ι → ℝ => T (Multiplicative.ofAdd t) w g) :
    ∃ n : ℕ, ∀ w ∈ W, ∃ (s : Finset (ι → ℂ)) (u : (ι → ℂ) → X → ℂ),
      w = ∑ μ ∈ s, u μ ∧ ∀ μ ∈ s, u μ ∈ W ∧ ∀ g,
        (fun t : ι → ℝ => T (Multiplicative.ofAdd t) (u μ) g *
          Complex.exp (-∑ i, (t i : ℂ) * μ i)) ∈ polynomialFunctions (ι → ℝ) n := by
  classical
  let d := Module.finrank ℂ W
  let b := Module.finBasis ℂ W
  let e : W ≃ₗ[ℂ] (Fin d → ℂ) := b.equivFun
  let π (t : ι → ℝ) : W →ₗ[ℂ] W := (T (Multiplicative.ofAdd t)).restrict (hW _)
  let A (t : ι → ℝ) : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ π t ∘ₗ e.symm.toLinearMap)
  have hA (t : ι → ℝ) (y : Fin d → ℂ) : A t y = e (π t (e.symm y)) := rfl
  have hπ (t : ι → ℝ) (w : W) : ((π t w : W) : X → ℂ) = T (Multiplicative.ofAdd t) w := rfl
  have hA0 : A 0 = 1 := by
    ext1 y
    rw [hA, _root_.one_apply_eq_self]
    have : π 0 (e.symm y) = e.symm y := by
      apply Subtype.ext
      rw [hπ, ofAdd_zero, map_one, Module.End.one_apply]
    rw [this, LinearEquiv.apply_symm_apply]
  have hAadd (s t : ι → ℝ) : A (s + t) = A s * A t := by
    ext1 y
    change A (s + t) y = A s (A t y)
    rw [hA, hA, hA, LinearEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [hπ, hπ, hπ, ofAdd_add, map_mul, Module.End.mul_apply]
  have hAcont : Continuous A := by
    apply continuous_clm_apply.mpr
    intro y
    have he : Continuous (e : W → (Fin d → ℂ)) :=
      LinearMap.continuous_of_finiteDimensional e.toLinearMap
    have hw : Continuous fun t : ι → ℝ => (π t (e.symm y) : W) :=
      (continuous_pi fun g => hcont _ (e.symm y).2 g).subtype_mk _
    exact he.comp hw
  obtain ⟨Xop, hXcomm, -, hAexp⟩ :=
    Langlands.Analysis.OneParameter.exists_exp_sum_of_continuous_add_mul A hAcont hA0 hAadd
  -- The joint generalized eigenspaces span.
  let f (i : ι) : Module.End ℂ (Fin d → ℂ) := (Xop i : Module.End ℂ (Fin d → ℂ))
  have hfcomm (i j : ι) : Commute (f i) (f j) := by
    change ((Xop i * Xop j : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ)) =
      ((Xop j * Xop i : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ))
    rw [(hXcomm i j).eq]
  have htop : ⨆ χ : ι → ℂ, ⨅ i, Module.End.maxGenEigenspace (f i) (χ i) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hfcomm i j) fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i)
  refine ⟨Module.finrank ℂ (Fin d → ℂ), fun w hw => ?_⟩
  have hv : e ⟨w, hw⟩ ∈ ⨆ χ : ι → ℂ, ⨅ i, Module.End.maxGenEigenspace (f i) (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc, hcsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hv
  refine ⟨c.support, fun μ => ((e.symm (c μ) : W) : X → ℂ), ?_, fun μ _ => ⟨(e.symm (c μ)).2,
    fun g => ?_⟩⟩
  · have h1 : (⟨w, hw⟩ : W) = ∑ μ ∈ c.support, e.symm (c μ) := by
      apply e.injective
      rw [map_sum]
      simp only [LinearEquiv.apply_symm_apply]
      rw [← hcsum]
      rfl
    have h2 := congrArg (fun x : W => (x : X → ℂ)) h1
    simpa only [Submodule.coe_sum] using h2
  · -- the polynomial orbit formula
    let ℓ : (Fin d → ℂ) →ₗ[ℂ] ℂ :=
      (LinearMap.proj g : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
    have hℓ (t : ι → ℝ) : T (Multiplicative.ofAdd t) ((e.symm (c μ) : W) : X → ℂ) g =
        ℓ (A t (c μ)) := by
      change _ = ((e.symm (e (π t (e.symm (c μ)))) : W) : X → ℂ) g
      rw [LinearEquiv.symm_apply_apply, hπ]
    have hformula (t : ι → ℝ) :
        T (Multiplicative.ofAdd t) ((e.symm (c μ) : W) : X → ℂ) g *
            Complex.exp (-∑ i, (t i : ℂ) * μ i) =
          ∑ k ∈ Finset.range (Module.finrank ℂ (Fin d → ℂ)), ((k.factorial : ℂ)⁻¹) *
            ℓ (((∑ i, (t i : ℂ) • (Xop i - μ i • 1)) ^ k) (c μ)) := by
      rw [hℓ, hAexp,
        Langlands.Analysis.OneParameter.exp_sum_smul_apply_of_mem Xop hXcomm μ t (hc μ), map_smul,
        map_sum, smul_eq_mul, mul_comm, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_mul]
      simp only [map_smul, smul_eq_mul]
    have hfun : (fun t : ι → ℝ => T (Multiplicative.ofAdd t) ((e.symm (c μ) : W) : X → ℂ) g *
          Complex.exp (-∑ i, (t i : ℂ) * μ i)) =
        ∑ k ∈ Finset.range (Module.finrank ℂ (Fin d → ℂ)), ((k.factorial : ℂ)⁻¹) •
          fun t : ι → ℝ => ℓ (((∑ i, (t i : ℂ) • (Xop i - μ i • 1)) ^ k) (c μ)) := by
      funext t
      rw [hformula]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
    exact polynomialFunctions_mono (Finset.mem_range.mp hk).le
      (linearForm_pow_sum_smul_mem_polynomialFunctions (fun i => Xop i - μ i • 1) ℓ k (c μ))

end Decomposition

end Langlands.Global
