import Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof

/-!
# Lemma (5.2) of Jacquet–Shalika I from bounds on finite self-pair Euler products

For a cuspidal realization `T` with unitary central character, a realization `Td` of its
contragredient, presentations `P`, `Pd` and a finite set `S` of finite places containing both
exceptional sets, the coefficients of the self-pair double series are `|tr A_v ^ k|² / k ≥ 0`.

* `partialEulerFactor_real`: at a real point `σ > 1`, the local factor `L(σ, π_v × π̃_v)` is
  `exp a_v`, with `a_v ≥ 0` the sum of the local self-pair series.
* `summableAt_of_prod_bound`: if the finite partial products at `σ` are bounded, the
  self-pair double series converges at `σ`.
* `continuation_of_summableAt`: if the self-pair double series converges at every real
  `σ > 1`, the partial Euler product converges absolutely on `Re s > 1` to
  `exp (∑ selfCoeff · q^(-ks))`, which is holomorphic there.
* `continuation_of_prod_bound`: the conclusion of `CuspidalSelfPairContinuationStatement` for
  `T, Td, P, Pd, S` from bounds on the finite partial products at every real `σ > 1`.

See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairFunctionalEquation CuspidalPairBoundaryNonvanishing
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalSelfPairAssembly

open CuspidalPairAbsoluteConvergence

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T Td : CuspidalOperatorRealization F r}
  (hT : HasUnitaryCentralCharacter T) (hTd : Td.realization.IsContragredientOf T.realization)
  (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
  {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)

omit [CompactSpace (AdeleQuotient F)] in
theorem logExponent_nonneg (x : {v : FinitePlace F // v ∉ S} × ℕ) : 0 ≤ logExponent x :=
  (Real.log_pos one_lt_two).le.trans (log_two_le_logExponent x)

include hT in
/-- The bounds `|α| ≤ q_v ^ (1/2)` for `P` outside `S` (Jacquet–Shalika I, Corollary (2.5)). -/
theorem bound_P : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
    Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
    ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) :=
  fun v _ _ hα => norm_eigenvalue_le_sqrt hT P v _ hα

include hT hTd hP in
/-- The bounds `|α| ≤ q_v ^ (1/2)` for the contragredient presentation `Pd` outside `S`: its
spectrum is the complex conjugate of that of `P`. -/
theorem bound_Pd : ∀ v (hv : v ∉ S), ∀ α ∈
    ((Pd.spectralSystem.eigenvalues v (fun h => hv (hPd h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
    ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) := by
  intro v hv α hα
  have hc := eigenvalues_eq_conjSpectrum hT hTd P Pd v (fun h => hv (hP h))
    (fun h => hv (hPd h))
  have hα' := (congrArg (fun e : Unramified.Eigenvalues (r + 1) => α ∈ (e : Multiset ℂˣ))
    hc).mp hα
  exact norm_conjSpectrum_le _ (fun β hβ => norm_eigenvalue_le_sqrt hT P v _ hβ) α hα'

include hT hTd in
/-- The self-pair term of the double series is the term of the general Dirichlet series with
the nonnegative coefficients `selfCoeff`. -/
theorem logEulerTerm_eq_term (x : {v : FinitePlace F // v ∉ S} × ℕ) (s : ℂ) :
    logEulerTerm P Pd hP hPd x.1 x.2 s =
      GeneralDirichlet.term (selfCoeff P hP) logExponent x s :=
  logEulerTerm_self_eq hT hTd P Pd hP hP hPd x.1.1 x.1.2 x.1.2 x.2 s

include hT hTd in
/-- **The self-pair product from the self-pair series.** If the self-pair double series
converges at every real `σ > 1`, then on `Re s > 1` the partial Euler product of `π × π̃`
converges absolutely to `exp` of the series, which is holomorphic there. -/
theorem continuation_of_summableAt
    (h : ∀ σ : ℝ, 1 < σ → GeneralDirichlet.SummableAt (selfCoeff P hP) logExponent σ) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 1 < s.re} ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Summable (fun v => ‖partialEulerFactor P Pd hP hPd v s - 1‖) ∧
          HasProd (fun v => partialEulerFactor P Pd hP hPd v s) (L s) := by
  refine ⟨fun s => Complex.exp (GeneralDirichlet.series (selfCoeff P hP) logExponent s),
    ?_, 1, fun s hs => ?_⟩
  · exact (GeneralDirichlet.differentiableOn_series logExponent_nonneg
      (selfCoeff_nonneg P hP) h).cexp
  · have hsum : Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
        ‖logEulerTerm P Pd hP hPd x.1 x.2 s‖ := by
      refine (h s.re hs).congr fun x => ?_
      rw [logEulerTerm_eq_term hT hTd P Pd hP hPd, GeneralDirichlet.norm_term,
        abs_of_nonneg (selfCoeff_nonneg P hP x)]
    obtain ⟨h2, h3⟩ := summable_and_hasProd_of_summable P Pd hP hPd (bound_P hT P hP)
      (bound_Pd hT hTd P Pd hP hPd) hs hsum
    refine ⟨h2, ?_⟩
    have he : (∑' x : {v : FinitePlace F // v ∉ S} × ℕ, logEulerTerm P Pd hP hPd x.1 x.2 s) =
        GeneralDirichlet.series (selfCoeff P hP) logExponent s := by
      rw [GeneralDirichlet.series]
      exact tsum_congr fun x => logEulerTerm_eq_term hT hTd P Pd hP hPd x s
    show HasProd _ (Complex.exp (GeneralDirichlet.series (selfCoeff P hP) logExponent s))
    rw [← he]
    exact h3

include hT hTd in
/-- At a real point `σ > 1`, the local self-pair factor is `exp a_v`, where `a_v ≥ 0` is the
sum of the local series `∑_k |tr A_v ^ k|² q_v ^ (-kσ) / k` (Jacquet–Shalika I, (5.3.1)). -/
theorem partialEulerFactor_real (v : {v : FinitePlace F // v ∉ S}) {σ : ℝ} (hσ : 1 < σ) :
    ∃ a : ℝ, HasSum (fun n : ℕ => selfCoeff P hP (v, n) * Real.exp (-logExponent (v, n) * σ)) a ∧
      partialEulerFactor P Pd hP hPd v σ = Complex.exp a := by
  obtain ⟨w, hw, he⟩ := exists_hasSum_logEulerTerm P Pd hP hPd (bound_P hT P hP)
    (bound_Pd hT hTd P Pd hP hPd) v (s := (σ : ℂ)) (by rw [Complex.ofReal_re]; exact hσ)
  have hw' : HasSum (fun n : ℕ =>
      ((selfCoeff P hP (v, n) * Real.exp (-logExponent (v, n) * σ) : ℝ) : ℂ)) w := by
    refine hw.congr_fun fun n => ?_
    rw [← GeneralDirichlet.term_ofReal]
    exact (logEulerTerm_eq_term hT hTd P Pd hP hPd (v, n) σ).symm
  have hs : Summable fun n : ℕ => selfCoeff P hP (v, n) * Real.exp (-logExponent (v, n) * σ) :=
    Complex.summable_ofReal.mp hw'.summable
  refine ⟨_, hs.hasSum, ?_⟩
  rw [he, hw'.unique (Complex.hasSum_ofReal.mpr hs.hasSum)]

include hT hTd in
/-- **Bounded finite products give convergence.** If at the real point `σ > 1` the finite
partial products `∏_(v ∈ E) L(σ, π_v × π̃_v)` are bounded, the self-pair double series
converges at `σ`. -/
theorem summableAt_of_prod_bound {σ : ℝ} (hσ : 1 < σ) {M : ℝ}
    (hM : ∀ E : Finset {v : FinitePlace F // v ∉ S},
      ‖∏ v ∈ E, partialEulerFactor P Pd hP hPd v σ‖ ≤ M) :
    GeneralDirichlet.SummableAt (selfCoeff P hP) logExponent σ := by
  choose a ha he using fun v => partialEulerFactor_real hT hTd P Pd hP hPd v hσ
  have hg : 0 ≤ fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
      selfCoeff P hP x * Real.exp (-logExponent x * σ) :=
    fun x => mul_nonneg (selfCoeff_nonneg P hP x) (Real.exp_pos _).le
  have hMpos : 0 < M := by
    have h := hM ∅
    rw [Finset.prod_empty, norm_one] at h
    linarith
  have hsumE : ∀ E : Finset {v : FinitePlace F // v ∉ S}, ∑ v ∈ E, a v ≤ Real.log M := by
    intro E
    have h := hM E
    rw [Finset.prod_congr rfl (fun v _ => he v), ← Complex.exp_sum, Complex.norm_exp,
      Complex.re_sum] at h
    simp only [Complex.ofReal_re] at h
    exact (Real.le_log_iff_exp_le hMpos).mpr h
  have ha0 : 0 ≤ a := fun v => (ha v).nonneg fun n => hg (v, n)
  have hA : Summable a := summable_of_sum_le ha0 hsumE
  show Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
    selfCoeff P hP x * Real.exp (-logExponent x * σ)
  refine (summable_prod_of_nonneg hg).mpr ⟨fun v => (ha v).summable, ?_⟩
  exact hA.congr fun v => ((ha v).tsum_eq).symm

include hT hTd in
/-- **Lemma (5.2) for the given data from bounded finite products.** If for every real
`σ > 1` the finite partial products of `L^S(σ, π × π̃)` are bounded, then the conclusion of
`CuspidalSelfPairContinuationStatement` holds for `T, Td, P, Pd, S`. -/
theorem continuation_of_prod_bound
    (hB : ∀ σ : ℝ, 1 < σ → ∃ M : ℝ, ∀ E : Finset {v : FinitePlace F // v ∉ S},
      ‖∏ v ∈ E, partialEulerFactor P Pd hP hPd v σ‖ ≤ M) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 1 < s.re} ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Summable (fun v => ‖partialEulerFactor P Pd hP hPd v s - 1‖) ∧
          HasProd (fun v => partialEulerFactor P Pd hP hPd v s) (L s) :=
  continuation_of_summableAt hT hTd P Pd hP hPd fun σ hσ =>
    let ⟨_, hM⟩ := hB σ hσ
    summableAt_of_prod_bound hT hTd P Pd hP hPd hσ hM

/-- The norm of a finite partial product is `exp` of the sum of the real local logarithms. -/
theorem norm_prod_eq_exp {σ : ℝ} {a : {v : FinitePlace F // v ∉ S} → ℝ}
    (he : ∀ v, partialEulerFactor P Pd hP hPd v σ = Complex.exp (a v))
    (E : Finset {v : FinitePlace F // v ∉ S}) :
    ‖∏ v ∈ E, partialEulerFactor P Pd hP hPd v σ‖ = Real.exp (∑ v ∈ E, a v) := by
  rw [Finset.prod_congr rfl (fun v _ => he v), ← Complex.exp_sum, Complex.norm_exp,
    Complex.re_sum]
  simp only [Complex.ofReal_re]

include hT hTd in
/-- **Changing `S`.** Let `S₁` be another finite set containing the exceptional sets (in the
application `S₁ ⊇ S`). If at a real point `σ > 1` the finite partial products over places
outside `S₁` are bounded, so are the finite partial products over places outside `S`: the
factors at the finitely many places of `S₁ \ S` are `exp a_v` with `a_v ≥ 0`. -/
theorem prod_bound_of_other {S₁ : Finset (FinitePlace F)}
    (hP₁ : P.exceptional ⊆ S₁) (hPd₁ : Pd.exceptional ⊆ S₁) {σ : ℝ} (hσ : 1 < σ) {M : ℝ}
    (hM : ∀ E : Finset {v : FinitePlace F // v ∉ S₁},
      ‖∏ v ∈ E, partialEulerFactor P Pd hP₁ hPd₁ v σ‖ ≤ M) :
    ∃ M' : ℝ, ∀ E : Finset {v : FinitePlace F // v ∉ S},
      ‖∏ v ∈ E, partialEulerFactor P Pd hP hPd v σ‖ ≤ M' := by
  classical
  choose a ha he using fun v => partialEulerFactor_real hT hTd P Pd hP hPd v hσ
  have ha0 : ∀ v, 0 ≤ a v := fun v => (ha v).nonneg fun n =>
    mul_nonneg (selfCoeff_nonneg P hP (v, n)) (Real.exp_pos _).le
  have hM0 : 0 ≤ M := by
    have h := hM ∅
    rw [Finset.prod_empty, norm_one] at h
    linarith
  set K : Finset {v : FinitePlace F // v ∉ S} := S₁.subtype fun v => v ∉ S with hK
  refine ⟨M * Real.exp (∑ v ∈ K, a v), fun E => ?_⟩
  rw [← Finset.prod_filter_mul_prod_filter_not E (fun v => v.1 ∉ S₁), norm_mul]
  have h₁ : ‖∏ v ∈ E.filter (fun v => v.1 ∉ S₁), partialEulerFactor P Pd hP hPd v σ‖ ≤ M := by
    let g : {x // x ∈ E.filter (fun v => v.1 ∉ S₁)} → {v : FinitePlace F // v ∉ S₁} :=
      fun v => ⟨v.1.1, (Finset.mem_filter.mp v.2).2⟩
    have hinj : Set.InjOn g ((E.filter (fun v => v.1 ∉ S₁)).attach : Set _) := by
      intro x _ y _ hxy
      have h : (g x).1 = (g y).1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    have hprod : ∏ v ∈ E.filter (fun v => v.1 ∉ S₁), partialEulerFactor P Pd hP hPd v σ =
        ∏ v ∈ (E.filter (fun v => v.1 ∉ S₁)).attach.image g,
          partialEulerFactor P Pd hP₁ hPd₁ v σ := by
      rw [Finset.prod_image hinj, ← Finset.prod_attach]
      rfl
    rw [hprod]
    exact hM _
  have h₂ : ‖∏ v ∈ E.filter (fun v => ¬ v.1 ∉ S₁), partialEulerFactor P Pd hP hPd v σ‖ ≤
      Real.exp (∑ v ∈ K, a v) := by
    rw [norm_prod_eq_exp P Pd hP hPd he]
    refine Real.exp_le_exp.mpr (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ => ha0 v)
    intro v hv
    rw [hK, Finset.mem_subtype]
    exact not_not.mp (Finset.mem_filter.mp hv).2
  calc _ ≤ M * Real.exp (∑ v ∈ K, a v) :=
        mul_le_mul h₁ h₂ (norm_nonneg _) hM0

include hT hTd in
/-- **Lemma (5.2) for the given data from bounded finite products outside another set.**
If `S₁` is a finite set containing the exceptional sets and for every real `σ > 1` the
finite partial products over places outside `S₁` are bounded, then the conclusion of
`CuspidalSelfPairContinuationStatement` holds for `T, Td, P, Pd, S`. -/
theorem continuation_of_prod_bound_other {S₁ : Finset (FinitePlace F)}
    (hP₁ : P.exceptional ⊆ S₁) (hPd₁ : Pd.exceptional ⊆ S₁)
    (hB : ∀ σ : ℝ, 1 < σ → ∃ M : ℝ, ∀ E : Finset {v : FinitePlace F // v ∉ S₁},
      ‖∏ v ∈ E, partialEulerFactor P Pd hP₁ hPd₁ v σ‖ ≤ M) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 1 < s.re} ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Summable (fun v => ‖partialEulerFactor P Pd hP hPd v s - 1‖) ∧
          HasProd (fun v => partialEulerFactor P Pd hP hPd v s) (L s) :=
  continuation_of_prod_bound hT hTd P Pd hP hPd fun σ hσ =>
    let ⟨_, hM⟩ := hB σ hσ
    prod_bound_of_other hT hTd P Pd hP hPd hP₁ hPd₁ hσ hM

end CuspidalSelfPairAssembly

end Langlands.Global
