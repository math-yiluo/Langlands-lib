import Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction
import Langlands.Global.Factors.HeckeEulerProduct

/-!
# Reduction of the completed Rankin–Selberg equation of cuspidal pairs

`CuspidalPairCompletedEquationStatement` splits into two parts:

* `CuspidalSatakeBoundStatement`: the Satake parameters of a cuspidal spectral presentation
  with irreducible admissible finite components are bounded by a fixed power `q_v ^ C` of the
  residue cardinality;
* `CuspidalPairContinuationStatement`: meromorphic continuation and functional equation of
  the completed L-functions, where the identification with the finite Euler products on a
  right half-plane is only required where these products converge
  (`FinitePairFactorChoice.ContinuationHolds`).

The absolute convergence of the Euler products is proved here from the Satake bound
(`FinitePairFactorChoice.summable_of_hasSatakeBound`), and
`cuspidalPairCompletedEquationReduction` proves that the two parts imply the target.
See the paired Markdown for the sources and the provenance of the split.
-/

noncomputable section

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation Polynomial
open LocalFactor.Archimedean
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

namespace CuspidalPairEulerConvergence

/-- `‖∏ (1 - z) - 1‖ ≤ (2 ^ #M - 1) ε` when every `z ∈ M` has `‖z‖ ≤ ε ≤ 1`. -/
theorem norm_prod_one_sub_sub_one_le (M : Multiset ℂ) {ε : ℝ} (hε : ε ≤ 1)
    (hM : ∀ z ∈ M, ‖z‖ ≤ ε) :
    ‖(M.map (fun z => 1 - z)).prod - 1‖ ≤ (2 ^ Multiset.card M - 1) * ε := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have ha : ‖a‖ ≤ ε := hM a (Multiset.mem_cons_self a M)
    have ih' := ih (fun z hz => hM z (Multiset.mem_cons_of_mem hz))
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    have hk : (1 : ℝ) ≤ 2 ^ Multiset.card M := one_le_pow₀ (by norm_num)
    have h1a : ‖1 - a‖ ≤ 2 := by
      calc ‖1 - a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    calc ‖(1 - a) * (M.map (fun z => 1 - z)).prod - 1‖
        = ‖(1 - a) * ((M.map (fun z => 1 - z)).prod - 1) - a‖ := by ring_nf
      _ ≤ ‖1 - a‖ * ‖(M.map (fun z => 1 - z)).prod - 1‖ + ‖a‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ 2 * ((2 ^ Multiset.card M - 1) * ε) + ε := by
          gcongr
      _ = (2 ^ (Multiset.card M + 1) - 1) * ε := by ring

/-- `‖P⁻¹ - 1‖ ≤ 2 ‖P - 1‖` when `‖P - 1‖ ≤ 1/2`. -/
theorem norm_inv_sub_one_le {P : ℂ} (h : ‖P - 1‖ ≤ 1 / 2) : ‖P⁻¹ - 1‖ ≤ 2 * ‖P - 1‖ := by
  have hP : (1 / 2 : ℝ) ≤ ‖P‖ := by
    have h1 : ‖(1 : ℂ)‖ - ‖P‖ ≤ ‖1 - P‖ := norm_sub_norm_le 1 P
    rw [norm_one, norm_sub_rev] at h1
    linarith
  have hPpos : 0 < ‖P‖ := by linarith
  have hP0 : P ≠ 0 := norm_pos_iff.mp hPpos
  rw [show P⁻¹ - 1 = -(P - 1) / P by field_simp; ring, norm_div, norm_neg,
    div_le_iff₀ hPpos]
  nlinarith [norm_nonneg (P - 1)]

/-- The value of the pair Euler polynomial at `x` is `∏_(i,j) (1 - a_i b_j x)`. -/
theorem eval_pairEulerPolynomial {n m : ℕ} (a : Unramified.Eigenvalues n)
    (b : Unramified.Eigenvalues m) (x : ℂ) :
    (pairEulerPolynomial a b).eval x =
      ((((a : Multiset ℂˣ) ×ˢ (b : Multiset ℂˣ)).map
        (fun z : ℂˣ × ℂˣ => (z.1 : ℂ) * z.2 * x)).map (fun w => 1 - w)).prod := by
  rw [pairEulerPolynomial, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp

/-- The local estimate: if every `‖a_i b_j x‖ ≤ ε` and `2 ^ (n m) ε ≤ 1/2`, then
`‖P(x)⁻¹ - 1‖ ≤ 2 ^ (n m + 1) ε` for the pair Euler polynomial `P` of `a` and `b`. -/
theorem norm_inv_eval_pairEulerPolynomial_sub_one_le {n m : ℕ} (a : Unramified.Eigenvalues n)
    (b : Unramified.Eigenvalues m) (x : ℂ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hab : ∀ α ∈ (a : Multiset ℂˣ), ∀ β ∈ (b : Multiset ℂˣ), ‖(α : ℂ) * β * x‖ ≤ ε)
    (hε : 2 ^ (n * m) * ε ≤ 1 / 2) :
    ‖((pairEulerPolynomial a b).eval x)⁻¹ - 1‖ ≤ 2 ^ (n * m + 1) * ε := by
  rw [eval_pairEulerPolynomial]
  have hcard : Multiset.card (((a : Multiset ℂˣ) ×ˢ (b : Multiset ℂˣ)).map
      (fun z : ℂˣ × ℂˣ => (z.1 : ℂ) * z.2 * x)) = n * m := by
    rw [Multiset.card_map, Multiset.card_product, Sym.card_coe, Sym.card_coe]
  have hM : ∀ w ∈ ((a : Multiset ℂˣ) ×ˢ (b : Multiset ℂˣ)).map
      (fun z : ℂˣ × ℂˣ => (z.1 : ℂ) * z.2 * x), ‖w‖ ≤ ε := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [Multiset.mem_product] at hz
    exact hab z.1 hz.1 z.2 hz.2
  have hpow : (1 : ℝ) ≤ 2 ^ (n * m) := one_le_pow₀ (by norm_num)
  have hε1 : ε ≤ 1 := by nlinarith
  have h1 := norm_prod_one_sub_sub_one_le _ hε1 hM
  rw [hcard] at h1
  have h2 := norm_inv_sub_one_le (h1.trans (by nlinarith))
  calc _ ≤ _ := h2
    _ ≤ 2 * ((2 ^ (n * m) - 1) * ε) := by gcongr
    _ ≤ 2 ^ (n * m + 1) * ε := by rw [pow_succ]; nlinarith

section Global

variable {F : Type u} [Field F] [NumberField F]

/-- The residue cardinality `q_v` is the absolute norm of `v`. -/
theorem residueCardinality_eq_absNorm (v : FinitePlace F) :
    residueCardinality v = Ideal.absNorm v.asIdeal :=
  HeckeEulerProduct.residueCardinality_eq v

theorem two_le_residueCardinality (v : FinitePlace F) : 2 ≤ residueCardinality v := by
  rw [residueCardinality_eq_absNorm]
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

/-- `‖q_v ^ (-s)‖ = q_v ^ (-Re s)`. -/
theorem norm_spectralPoint (v : FinitePlace F) (s : ℂ) :
    ‖RankinSelberg.spectralPoint (residueCardinality v) s‖ =
      (residueCardinality v : ℝ) ^ (-s.re) := by
  unfold RankinSelberg.spectralPoint
  rw [Complex.norm_natCast_cpow_of_pos (by have := two_le_residueCardinality v; omega),
    Complex.neg_re]

/-- Away from a finite set `S`, let `L_v` be the pair Euler polynomial of Satake multisets
`a_v`, `b_v` of sizes `n`, `m` with `‖a_(v,i)‖ ≤ q_v ^ A` and `‖b_(v,j)‖ ≤ q_v ^ B`. Then
`∑_v ‖L_v(q_v ^ (-s))⁻¹ - 1‖` converges for `Re s > A + B + n m + 1`. -/
theorem summable_norm_inv_eval_sub_one (S : Finset (FinitePlace F)) {n m : ℕ}
    (L : FinitePlace F → ℂ[X]) (a : ∀ v, v ∉ S → Unramified.Eigenvalues n)
    (b : ∀ v, v ∉ S → Unramified.Eigenvalues m)
    (hL : ∀ v (hv : v ∉ S), L v = pairEulerPolynomial (a v hv) (b v hv)) {A B : ℝ}
    (hA : ∀ v (hv : v ∉ S), ∀ α ∈ (a v hv : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ A)
    (hB : ∀ v (hv : v ∉ S), ∀ β ∈ (b v hv : Multiset ℂˣ),
      ‖(β : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ B)
    {s : ℂ} (hs : A + B + ((n * m + 1 : ℕ) : ℝ) < s.re) :
    Summable (fun v =>
      ‖((L v).eval (RankinSelberg.spectralPoint (residueCardinality v) s))⁻¹ - 1‖) := by
  have hN : (1 : ℝ) ≤ ((n * m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hδ1 : 1 < s.re - A - B := by linarith
  refine Summable.of_norm_bounded_eventually
    ((HeckeEulerProduct.summable_absNorm_rpow (K := F) hδ1).mul_left (2 ^ (n * m + 1))) ?_
  filter_upwards [S.eventually_cofinite_notMem] with v hv
  have hq2 : (2 : ℝ) ≤ (residueCardinality v : ℝ) := by
    exact_mod_cast two_le_residueCardinality v
  have hq0 : (0 : ℝ) < (residueCardinality v : ℝ) := by linarith
  have hab : ∀ α ∈ (a v hv : Multiset ℂˣ), ∀ β ∈ (b v hv : Multiset ℂˣ),
      ‖(α : ℂ) * β * RankinSelberg.spectralPoint (residueCardinality v) s‖ ≤
        (residueCardinality v : ℝ) ^ (-(s.re - A - B)) := by
    intro α hα β hβ
    rw [norm_mul, norm_mul, norm_spectralPoint]
    calc ‖(α : ℂ)‖ * ‖(β : ℂ)‖ * (residueCardinality v : ℝ) ^ (-s.re)
        ≤ (residueCardinality v : ℝ) ^ A * (residueCardinality v : ℝ) ^ B *
            (residueCardinality v : ℝ) ^ (-s.re) := by
          gcongr
          · exact hA v hv α hα
          · exact hB v hv β hβ
      _ = (residueCardinality v : ℝ) ^ (-(s.re - A - B)) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
          congr 1
          ring
  have hε : 2 ^ (n * m) * (residueCardinality v : ℝ) ^ (-(s.re - A - B)) ≤ 1 / 2 := by
    have h1 : (residueCardinality v : ℝ) ^ (-(s.re - A - B)) ≤
        (residueCardinality v : ℝ) ^ (-((n * m + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg hq0.le ((n * m + 1 : ℕ) : ℝ), Real.rpow_natCast] at h1
    have h2 : (2 : ℝ) ^ (n * m + 1) ≤ (residueCardinality v : ℝ) ^ (n * m + 1) :=
      pow_le_pow_left₀ (by norm_num) hq2 _
    calc 2 ^ (n * m) * (residueCardinality v : ℝ) ^ (-(s.re - A - B))
        ≤ 2 ^ (n * m) * ((residueCardinality v : ℝ) ^ (n * m + 1))⁻¹ := by gcongr
      _ ≤ 2 ^ (n * m) * ((2 : ℝ) ^ (n * m + 1))⁻¹ := by gcongr
      _ = 1 / 2 := by rw [pow_succ]; field_simp
  have key := norm_inv_eval_pairEulerPolynomial_sub_one_le (a v hv) (b v hv)
    (RankinSelberg.spectralPoint (residueCardinality v) s) (by positivity) hab hε
  rw [norm_norm, hL v hv]
  refine key.trans (le_of_eq ?_)
  rw [residueCardinality_eq_absNorm]

/-- An absolutely convergent product `∑ ‖f i - 1‖ < ∞` of complex numbers has a value. -/
theorem hasProd_of_summable_norm_sub_one {ι : Type*} {f : ι → ℂ}
    (hf : Summable fun i => ‖f i - 1‖) : HasProd f (∏' i, f i) := by
  have hm := multipliable_one_add_of_summable (f := fun i => f i - 1) hf
  have he : (fun i => 1 + (f i - 1)) = f := by
    funext i
    ring
  rw [he] at hm
  exact hm.hasProd

end Global

end CuspidalPairEulerConvergence

namespace CuspidalPairFunctionalEquation

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T Td : CuspidalOperatorRealization F r}
  {T' Td' : CuspidalOperatorRealization F t}

/-- The Satake parameters of `P` at every place outside its exceptional set are bounded by
`q_v ^ C`. -/
def HasSatakeBound (P : CuspidalSpectralPresentation.{u, uQ} T) (C : ℝ) : Prop :=
  ∀ (v : FinitePlace F) (hv : v ∉ P.exceptional),
    ∀ α ∈ ((P.spectralSystem.eigenvalues v hv : Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ C

namespace FinitePairFactorChoice

variable {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {P : CuspidalSpectralPresentation.{u, uQ} T}
  {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
  {Pd' : CuspidalSpectralPresentation.{u, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}
  (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')

/-- Continuation and functional equation without convergence: there are a real `σ` and
functions `Λ`, `Λd`, meromorphic on `ℂ`, such that for `Re s > σ`, whenever the finite Euler
products of the pair and of the contragredient pair converge to `p` and `pd`, then
`Λ(s) = Linf(s) p` and `Λd(s) = Ldinf(s) pd`; and off a discrete set
`Λ(s) = (∏_(v ∈ S) ε_v(s)) ε_∞(s) Λd(1 - s)`. -/
def ContinuationHolds (S : Finset (FinitePlace F)) (Linf Ldinf εinf : ℂ → ℂ) : Prop :=
  ∃ (σ : ℝ) (Λ Λd : ℂ → ℂ),
    MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λd Set.univ ∧
    (∀ s : ℂ, σ < s.re → ∀ p pd : ℂ, HasProd (fun v => c.finiteL v s) p →
      HasProd (fun v => c.finiteDualL v s) pd → Λ s = Linf s * p ∧ Λd s = Ldinf s * pd) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      Λ s = (∏ v ∈ S, c.finiteEpsilon v s) * εinf s * Λd (1 - s)

/-- Absolute convergence of both finite Euler products: if the factor choice is unramified
outside `S` and the Satake parameters of the four presentations are bounded by `q_v ^ A`,
`q_v ^ B`, `q_v ^ Ad`, `q_v ^ Bd`, then `∑_v ‖L_v(s) - 1‖` and `∑_v ‖L∨_v(s) - 1‖` converge
for `Re s > max (A + B) (Ad + Bd) + (r + 1)(t + 1) + 1`. -/
theorem summable_of_hasSatakeBound {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)
    (hPd' : Pd'.exceptional ⊆ S) (hc : c.IsUnramifiedOutside S) {A B Ad Bd : ℝ}
    (hA : HasSatakeBound P A) (hB : HasSatakeBound P' B) (hAd : HasSatakeBound Pd Ad)
    (hBd : HasSatakeBound Pd' Bd) {s : ℂ}
    (hs : max (A + B) (Ad + Bd) + (((r + 1) * (t + 1) + 1 : ℕ) : ℝ) < s.re) :
    Summable (fun v => ‖c.finiteL v s - 1‖) ∧
      Summable (fun v => ‖c.finiteDualL v s - 1‖) := by
  have h1 := le_max_left (A + B) (Ad + Bd)
  have h2 := le_max_right (A + B) (Ad + Bd)
  constructor
  · exact CuspidalPairEulerConvergence.summable_norm_inv_eval_sub_one S c.lPolynomial
      (fun v hv => P.spectralSystem.eigenvalues v (fun hm => hv (hP hm)))
      (fun v hv => P'.spectralSystem.eigenvalues v (fun hm => hv (hP' hm)))
      (fun v hv => (hc v hv).1 _ _) (fun v _ => hA v _) (fun v _ => hB v _) (by linarith)
  · exact CuspidalPairEulerConvergence.summable_norm_inv_eval_sub_one S c.dualLPolynomial
      (fun v hv => Pd.spectralSystem.eigenvalues v (fun hm => hv (hPd hm)))
      (fun v hv => Pd'.spectralSystem.eigenvalues v (fun hm => hv (hPd' hm)))
      (fun v hv => (hc v hv).2.1 _ _) (fun v _ => hAd v _) (fun v _ => hBd v _)
      (by linarith)

/-- Continuation and the Satake bounds give the completed equation. -/
theorem completedEquationHolds_of_continuationHolds {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)
    (hPd' : Pd'.exceptional ⊆ S) (hc : c.IsUnramifiedOutside S) {A B Ad Bd : ℝ}
    (hA : HasSatakeBound P A) (hB : HasSatakeBound P' B) (hAd : HasSatakeBound Pd Ad)
    (hBd : HasSatakeBound Pd' Bd) {Linf Ldinf εinf : ℂ → ℂ}
    (hcont : c.ContinuationHolds S Linf Ldinf εinf) :
    c.CompletedEquationHolds S Linf Ldinf εinf := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hprod, hfe⟩ := hcont
  refine ⟨max σ (max (A + B) (Ad + Bd) + (((r + 1) * (t + 1) + 1 : ℕ) : ℝ)), Λ, Λd, hΛ, hΛd,
    fun s hs => ?_, hfe⟩
  obtain ⟨hs1, hs2⟩ := c.summable_of_hasSatakeBound hP hP' hPd hPd' hc hA hB hAd hBd
    (lt_of_le_of_lt (le_max_right _ _) hs)
  have m1 := CuspidalPairEulerConvergence.hasProd_of_summable_norm_sub_one hs1
  have m2 := CuspidalPairEulerConvergence.hasProd_of_summable_norm_sub_one hs2
  exact ⟨hs1, hs2, _, _, m1, m2, hprod s (lt_of_le_of_lt (le_max_left _ _) hs) _ _ m1 m2⟩

end FinitePairFactorChoice

end CuspidalPairFunctionalEquation

/-- The Satake bound for cuspidal spectral presentations: for every actual cuspidal
realization of `GL_(r+1)` over a number field and every spectral presentation of it whose
finite components are irreducible and admissible, there is a real `C` such that every
Satake parameter `α` at every place `v` outside the exceptional set satisfies
`‖α‖ ≤ q_v ^ C`. -/
def CuspidalSatakeBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{u, uQ} T),
    HasIrreducibleAdmissibleComponents P → ∃ C : ℝ, HasSatakeBound P C

/-- Continuation and functional equation of cuspidal pairs: the data and hypotheses of
`CuspidalPairCompletedEquationStatement`, with the conclusion
`FinitePairFactorChoice.ContinuationHolds`, which identifies the completed L-functions with
the Euler products only where these converge. -/
def CuspidalPairContinuationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∃ x : Adeles F, ψ x ≠ 1) → (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r t : ℕ) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (hd : HasIrreducibleAdmissibleComponents Pd)
    (hd' : HasIrreducibleAdmissibleComponents Pd') (S : Finset (FinitePlace F)),
    P.exceptional ⊆ S → P'.exceptional ⊆ S → Pd.exceptional ⊆ S → Pd'.exceptional ⊆ S →
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd', c.IsUnramifiedOutside S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
  let infiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
  let dualInfiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
  let infiniteEpsilon (s : ℂ) : ℂ :=
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
      ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
        (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
  c.ContinuationHolds S infiniteL dualInfiniteL infiniteEpsilon

/-- The Satake bound and continuation imply the completed equation for every admissible
exceptional set. -/
def CuspidalPairCompletedEquationReductionStatement : Prop :=
  CuspidalSatakeBoundStatement.{u, uQ} →
    CuspidalPairContinuationStatement.{u, uQ} →
      CuspidalPairCompletedEquationStatement.{u, uQ}

/-- The reduction: the completed equation follows from the Satake bound and continuation. -/
theorem cuspidalPairCompletedEquationReduction :
    CuspidalPairCompletedEquationReductionStatement.{u, uQ} := by
  intro hSat hCont F _ _ _ ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd' S hP
    hP' hPd hPd' hsupp c hc aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd'
    hdC hdC' hdCd hdCd'
  obtain ⟨A, hA⟩ := hSat F r T P h
  obtain ⟨B, hB⟩ := hSat F t T' P' h'
  obtain ⟨Ad, hAd⟩ := hSat F r Td Pd hd
  obtain ⟨Bd, hBd⟩ := hSat F t Td' Pd' hd'
  exact c.completedEquationHolds_of_continuationHolds hP hP' hPd hPd' hc hA hB hAd hBd
    (hCont F ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd' S hP hP' hPd hPd'
      hsupp c hc aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC'
      hdCd hdCd')

end Langlands.Global
