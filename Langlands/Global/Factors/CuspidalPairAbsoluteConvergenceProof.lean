import Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceStatement
import Langlands.Global.Factors.CuspidalSatakeBoundReduction
import Langlands.Analysis.LandauDirichlet
import Langlands.Representation.Unramified.UnitarySpectrumConjugation
import Langlands.Representation.RankinSelberg.UnramifiedUnitaryPoleFreeProof
import Langlands.Automorphic.AssociatedGammaPrincipalSeries
import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityProof
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof

/-!
# Jacquet–Shalika I, Theorem (5.3), from Lemma (5.2)

This module proves `CuspidalPairAbsoluteConvergenceReductionStatement`
(`Langlands.Global.cuspidalPairAbsoluteConvergenceReduction`).

* Local logarithms of pair Euler factors (JS I, (5.3.1)).
* The bound `|α| ≤ q_v ^ (1/2)` for unitary cuspidal presentations (JS I, Corollary (2.5)),
  and the conjugate spectrum of a contragredient presentation.
* The product as the exponential of the double series (JS I, (5.3.2)).
* The self-pair series (5.3.3) through Landau's theorem and Lemma (5.2).
* Cauchy–Schwarz (5.3.5) and the conclusion.

See the paired Markdown for the route and its sources.
-/

noncomputable section
set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairFunctionalEquation CuspidalPairBoundaryNonvanishing
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPairAbsoluteConvergence

/-! ### Local logarithms of pair Euler factors -/

section LocalLog

open Unramified

/-- `∑_(k ≥ 0) w ^ (k + 1) / (k + 1) = -log (1 - w)` for `‖w‖ < 1`. -/
theorem hasSum_pow_succ_div (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => w ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - w)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hw
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
    sub_zero, Nat.cast_add, Nat.cast_one] at h'
  exact h'

/-- The logarithm series of a finite product `∏ (1 - w)⁻¹`. -/
theorem multiset_hasSum_log (M : Multiset ℂ) (hM : ∀ w ∈ M, ‖w‖ < 1) :
    HasSum (fun k : ℕ => (M.map fun w => w ^ (k + 1)).sum / ((k : ℂ) + 1))
      (M.map fun w => -Complex.log (1 - w)).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons w M ih =>
    have h1 := hasSum_pow_succ_div w (hM w (Multiset.mem_cons_self w M))
    have h2 := ih (fun x hx => hM x (Multiset.mem_cons_of_mem hx))
    convert h1.add h2 using 1
    · funext k
      rw [Multiset.map_cons, Multiset.sum_cons, add_div]
    · rw [Multiset.map_cons, Multiset.sum_cons]

theorem multiset_exp_log (M : Multiset ℂ) (hM : ∀ w ∈ M, ‖w‖ < 1) :
    Complex.exp (M.map fun w => -Complex.log (1 - w)).sum = ((M.map fun w => 1 - w).prod)⁻¹ := by
  rw [Complex.exp_multiset_sum, Multiset.map_map, ← Multiset.prod_map_inv]
  congr 1
  apply Multiset.map_congr rfl
  intro w hw
  have hw1 : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    have h' := hM w hw
    rw [this, norm_one] at h'
    exact lt_irrefl _ h'
  simp only [Function.comp_apply]
  rw [Complex.exp_neg, Complex.exp_log hw1]

/-- `∑_((α, β)) (α β x) ^ k = tr(a ^ k) tr(b ^ k) x ^ k`. -/
theorem sum_map_pow_product (a b : Multiset ℂˣ) (x : ℂ) (k : ℕ) :
    (((a ×ˢ b).map fun z : ℂˣ × ℂˣ => (z.1 : ℂ) * z.2 * x).map fun w => w ^ k).sum =
      (a.map fun z : ℂˣ => (z : ℂ) ^ k).sum * (b.map fun z : ℂˣ => (z : ℂ) ^ k).sum *
        x ^ k := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons α a ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.map_add, Multiset.sum_add, ih,
      Multiset.map_map, Multiset.map_map, Multiset.map_cons, Multiset.sum_cons]
    have e : ((fun w : ℂ => w ^ k) ∘ (fun z : ℂˣ × ℂˣ => (z.1 : ℂ) * z.2 * x)) ∘ Prod.mk α =
        fun β : ℂˣ => ((α : ℂ) ^ k * x ^ k) * (β : ℂ) ^ k := by
      funext β
      simp only [Function.comp_apply]
      ring
    rw [e, Multiset.sum_map_mul_left]
    ring

/-- **Local logarithms (Jacquet–Shalika I, (5.3.1)).** If every `‖α β x‖ < 1`, the inverse
pair Euler factor is `exp (∑_(k ≥ 1) tr(a ^ k) tr(b ^ k) x ^ k / k)`. -/
theorem exists_hasSum_pairLog {n m : ℕ} (a : Eigenvalues n) (b : Eigenvalues m) (x : ℂ)
    (h : ∀ α ∈ (a : Multiset ℂˣ), ∀ β ∈ (b : Multiset ℂˣ), ‖(α : ℂ) * β * x‖ < 1) :
    ∃ w : ℂ, HasSum (fun k : ℕ => a.powerTrace (k + 1) * b.powerTrace (k + 1) *
        x ^ (k + 1) / ((k : ℂ) + 1)) w ∧
      ((pairEulerPolynomial a b).eval x)⁻¹ = Complex.exp w := by
  set M : Multiset ℂ := ((a : Multiset ℂˣ) ×ˢ (b : Multiset ℂˣ)).map
    (fun z : ℂˣ × ℂˣ => (z.1 : ℂ) * z.2 * x) with hMdef
  have hM : ∀ w ∈ M, ‖w‖ < 1 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [Multiset.mem_product] at hz
    exact h z.1 hz.1 z.2 hz.2
  refine ⟨(M.map fun w => -Complex.log (1 - w)).sum, ?_, ?_⟩
  · convert multiset_hasSum_log M hM using 1
    funext k
    rw [hMdef, sum_map_pow_product]
    rfl
  · rw [multiset_exp_log M hM, CuspidalPairEulerConvergence.eval_pairEulerPolynomial]

end LocalLog

/-! ### The local unitary bounds for cuspidal presentations -/

section LocalBounds

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- **Jacquet–Shalika I, Corollary (2.5), in the non-strict form.** For a cuspidal realization
with unitary central character and a spectral presentation, every Satake parameter outside the
exceptional set has norm at most `q_v ^ (1/2)`. -/
theorem norm_eigenvalue_le_sqrt {r : ℕ} {T : CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T) (Q : CuspidalSpectralPresentation.{u, uQ} T)
    (v : FinitePlace F) (hv : v ∉ Q.exceptional) {α : ℂˣ}
    (hα : α ∈ ((Q.spectralSystem.eigenvalues v hv : Unramified.Eigenvalues (r + 1)) :
      Multiset ℂˣ)) :
    ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) := by
  have hI : (Q.localComponent v).IsIrreducible :=
    (Q.presentation.localComponent_isIrreducible_iff Q.finiteSlice.nonzero v).mpr
      (Q.unramified.irreducible v hv)
  have hA : (Q.localComponent v).IsAdmissible :=
    (Q.presentation.localComponent_isAdmissible_iff Q.finiteSlice.nonzero v).mpr
      (Q.unramified.admissible v hv)
  have hU := Automorphic.cuspidalUnitaryLocalUnitarity.{u, uQ} F r T hT Q v hI hA
  have hs : Unramified.HasSphericalHeckeSpectrum (CompletionPadic.padicField v)
      ((Q.localComponent v).padicObject hI hA) (Q.spectralSystem.eigenvalues v hv) :=
    Q.hasSpectrum v hv
  obtain ⟨z, hz, hsph⟩ :=
    Unramified.hasSphericalSpectrum_of_hasSphericalHeckeSpectrum (CompletionPadic.padicField v)
      _ _ hs
  let ψ := HeckeFunctionalEquation.standardFiniteAdditiveComponent F v
  have hα' : α ∈ List.ofFn z := by
    rw [← hz] at hα
    exact Multiset.mem_coe.mp hα
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' z α).mp hα'
  have hg := Automorphic.cuspidalUnitaryLocalGenericity F r T hT Q v hI hA ψ
  have hb := RankinSelberg.UnramifiedUnitary.norm_unramifiedClass_le_sqrt
    (CompletionPadic.padicField v) r ψ _ (Unramified.characterTuple (CompletionPadic.padicField v) z)
    ⟨hg, hsph.1, Unramified.characterTuple_isUnramified (CompletionPadic.padicField v) z,
      hsph.2⟩ hU j
  have hc := congrFun (Unramified.characterValues_characterTuple (CompletionPadic.padicField v) z) j
  have e : RankinSelberg.unramifiedClass (CompletionPadic.padicField v)
      (Unramified.characterTuple (CompletionPadic.padicField v) z) j = ((z j : ℂˣ) : ℂ) := by
    rw [← hc]
    rfl
  rw [e] at hb
  exact hb

/-- For a contragredient presentation of a cuspidal realization with unitary central
character, the spectrum is the complex conjugate one. -/
theorem eigenvalues_eq_conjSpectrum {r : ℕ} {T Td : CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T) (hTd : Td.realization.IsContragredientOf T.realization)
    (Q : CuspidalSpectralPresentation.{u, uQ} T) (Qd : CuspidalSpectralPresentation.{u, uQ} Td)
    (v : FinitePlace F) (hv : v ∉ Q.exceptional) (hvd : v ∉ Qd.exceptional) :
    Qd.spectralSystem.eigenvalues v hvd =
      Unramified.conjSpectrum (Q.spectralSystem.eigenvalues v hv) := by
  have hI : (Q.localComponent v).IsIrreducible :=
    (Q.presentation.localComponent_isIrreducible_iff Q.finiteSlice.nonzero v).mpr
      (Q.unramified.irreducible v hv)
  have hA : (Q.localComponent v).IsAdmissible :=
    (Q.presentation.localComponent_isAdmissible_iff Q.finiteSlice.nonzero v).mpr
      (Q.unramified.admissible v hv)
  have hU := Automorphic.cuspidalUnitaryLocalUnitarity.{u, uQ} F r T hT Q v hI hA
  have hs : Unramified.HasSphericalHeckeSpectrum (CompletionPadic.padicField v)
      ((Q.localComponent v).padicObject hI hA) (Q.spectralSystem.eigenvalues v hv) :=
    Q.hasSpectrum v hv
  rw [CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf T Td Q Qd hTd v
    hv hvd, Unramified.conjSpectrum_eq_map_inv_of_hasSphericalHeckeSpectrum _ _ hU hs]

end LocalBounds

/-! ### Norms of the terms of the double series -/

section Norms

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The exponent `(n + 1) log q_v` of the term `(v, n)` of the double series. -/
def logExponent {S : Finset (FinitePlace F)} (x : {v : FinitePlace F // v ∉ S} × ℕ) : ℝ :=
  ((x.2 : ℝ) + 1) * Real.log (residueCardinality x.1.1 : ℝ)

/-- The self-pair coefficient `|tr A_v ^ (n + 1)|² / (n + 1)`. -/
def selfCoeff {r : ℕ} {T : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{u, uQ} T) {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (x : {v : FinitePlace F // v ∉ S} × ℕ) : ℝ :=
  ‖P.spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hP h)) (x.2 + 1)‖ ^ 2 / ((x.2 : ℝ) + 1)

theorem selfCoeff_nonneg {r : ℕ} {T : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{u, uQ} T) {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (x : {v : FinitePlace F // v ∉ S} × ℕ) :
    0 ≤ selfCoeff P hP x :=
  div_nonneg (sq_nonneg _) (by positivity)

omit [CompactSpace (AdeleQuotient F)] in
theorem one_lt_residueCardinality (v : FinitePlace F) : (1 : ℝ) < residueCardinality v := by
  have h := CuspidalPairEulerConvergence.two_le_residueCardinality v
  have h' : (2 : ℝ) ≤ residueCardinality v := by exact_mod_cast h
  linarith

omit [CompactSpace (AdeleQuotient F)] in
theorem log_two_le_logExponent {S : Finset (FinitePlace F)}
    (x : {v : FinitePlace F // v ∉ S} × ℕ) : Real.log 2 ≤ logExponent x := by
  have hq : (2 : ℝ) ≤ residueCardinality x.1.1 := by
    exact_mod_cast CuspidalPairEulerConvergence.two_le_residueCardinality x.1.1
  have h1 : Real.log 2 ≤ Real.log (residueCardinality x.1.1 : ℝ) :=
    Real.log_le_log (by norm_num) hq
  have h2 : 0 ≤ Real.log (residueCardinality x.1.1 : ℝ) := (Real.log_pos (by linarith)).le
  have h3 : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg _
  unfold logExponent
  nlinarith

omit [CompactSpace (AdeleQuotient F)] in
theorem exp_neg_logExponent {S : Finset (FinitePlace F)}
    (x : {v : FinitePlace F // v ∉ S} × ℕ) (σ : ℝ) :
    Real.exp (-logExponent x * σ) = ((residueCardinality x.1.1 : ℝ) ^ (-σ)) ^ (x.2 + 1) := by
  have hq : (0 : ℝ) < residueCardinality x.1.1 := by
    linarith [one_lt_residueCardinality x.1.1]
  rw [Real.rpow_def_of_pos hq, ← Real.exp_nat_mul]
  congr 1
  unfold logExponent
  push_cast
  ring

omit [CompactSpace (AdeleQuotient F)] in
theorem norm_spectralPoint_pow (v : FinitePlace F) (s : ℂ) (n : ℕ) :
    ‖RankinSelberg.spectralPoint (residueCardinality v) s ^ (n + 1)‖ =
      ((residueCardinality v : ℝ) ^ (-s.re)) ^ (n + 1) := by
  rw [norm_pow, CuspidalPairEulerConvergence.norm_spectralPoint]

omit [CompactSpace (AdeleQuotient F)] in
theorem spectralPoint_pow_eq_exp {S : Finset (FinitePlace F)}
    (x : {v : FinitePlace F // v ∉ S} × ℕ) (s : ℂ) :
    RankinSelberg.spectralPoint (residueCardinality x.1.1) s ^ (x.2 + 1) =
      Complex.exp (-(logExponent x : ℂ) * s) := by
  have hq : (residueCardinality x.1.1 : ℂ) ≠ 0 := by
    have := one_lt_residueCardinality x.1.1
    exact_mod_cast (show (residueCardinality x.1.1 : ℝ) ≠ 0 by linarith)
  unfold RankinSelberg.spectralPoint
  rw [Complex.cpow_def_of_ne_zero hq, ← Complex.exp_nat_mul]
  congr 1
  unfold logExponent
  rw [← Complex.natCast_log]
  push_cast
  ring

/-- `‖tr(a ^ k)‖ ≤ n B ^ k` when every parameter has norm at most `B`. -/
theorem norm_powerTrace_le {n : ℕ} (a : Unramified.Eigenvalues n) {B : ℝ}
    (hB : ∀ α ∈ (a : Multiset ℂˣ), ‖(α : ℂ)‖ ≤ B) (k : ℕ) :
    ‖a.powerTrace k‖ ≤ n * B ^ k := by
  rw [Unramified.Eigenvalues.powerTrace]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  have h := Multiset.sum_le_card_nsmul (((a : Multiset ℂˣ)).map
    ((fun x : ℂ => ‖x‖) ∘ fun z : ℂˣ => (z : ℂ) ^ k)) (B ^ k) (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
      simp only [Function.comp_apply, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB z hz) k)
  rw [Multiset.card_map, Sym.card_coe, nsmul_eq_mul] at h
  exact h

theorem sqrt_pow_mul_rpow (q : ℝ) (hq : 0 < q) (σ : ℝ) (k : ℕ) :
    Real.sqrt q ^ k * Real.sqrt q ^ k * (q ^ (-σ)) ^ k = (q ^ (1 - σ)) ^ k := by
  rw [← mul_pow, ← mul_pow, Real.mul_self_sqrt hq.le]
  congr 1
  rw [show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hq, Real.rpow_one]

/-- The norm of a term of the double series. -/
theorem norm_logEulerTerm {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (x : {v : FinitePlace F // v ∉ S} × ℕ) (s : ℂ) :
    ‖logEulerTerm P P' hP hP' x.1 x.2 s‖ =
      ‖P.spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hP h)) (x.2 + 1)‖ *
        ‖P'.spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hP' h)) (x.2 + 1)‖ /
          ((x.2 : ℝ) + 1) * Real.exp (-logExponent x * s.re) := by
  rw [logEulerTerm, norm_div, norm_mul, norm_mul, norm_spectralPoint_pow,
    exp_neg_logExponent]
  have h : ‖((x.2 : ℂ) + 1)‖ = (x.2 : ℝ) + 1 := by
    rw [show ((x.2 : ℂ) + 1) = (((x.2 : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h]
  ring

/-- The geometric bound of a term of the double series, from the bounds `q_v ^ (1/2)`. -/
theorem norm_logEulerTerm_le {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPb : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (hP'b : ∀ v (hv : v ∉ S), ∀ α ∈ ((P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)) :
      Unramified.Eigenvalues (t + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (x : {v : FinitePlace F // v ∉ S} × ℕ) (s : ℂ) :
    ‖logEulerTerm P P' hP hP' x.1 x.2 s‖ ≤
      ((r + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) *
        ((residueCardinality x.1.1 : ℝ) ^ (1 - s.re)) ^ (x.2 + 1) := by
  have hq : (0 : ℝ) < residueCardinality x.1.1 := by
    linarith [one_lt_residueCardinality x.1.1]
  rw [norm_logEulerTerm, exp_neg_logExponent]
  have h1 := norm_powerTrace_le _ (hPb x.1.1 x.1.2) (x.2 + 1)
  have h2 := norm_powerTrace_le _ (hP'b x.1.1 x.1.2) (x.2 + 1)
  have hd : (1 : ℝ) ≤ (x.2 : ℝ) + 1 := by linarith [(Nat.cast_nonneg x.2 : (0 : ℝ) ≤ x.2)]
  have hpos : 0 ≤ ((residueCardinality x.1.1 : ℝ) ^ (-s.re)) ^ (x.2 + 1) := by positivity
  calc ‖P.spectralSystem.powerTrace x.1.1 _ (x.2 + 1)‖ *
        ‖P'.spectralSystem.powerTrace x.1.1 _ (x.2 + 1)‖ / ((x.2 : ℝ) + 1) *
          ((residueCardinality x.1.1 : ℝ) ^ (-s.re)) ^ (x.2 + 1)
      ≤ ‖P.spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hP h)) (x.2 + 1)‖ *
        ‖P'.spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hP' h)) (x.2 + 1)‖ *
          ((residueCardinality x.1.1 : ℝ) ^ (-s.re)) ^ (x.2 + 1) := by
        gcongr
        exact div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hd
    _ ≤ (((r + 1 : ℕ) : ℝ) * Real.sqrt (residueCardinality x.1.1 : ℝ) ^ (x.2 + 1)) *
        (((t + 1 : ℕ) : ℝ) * Real.sqrt (residueCardinality x.1.1 : ℝ) ^ (x.2 + 1)) *
          ((residueCardinality x.1.1 : ℝ) ^ (-s.re)) ^ (x.2 + 1) := by
        gcongr
        · exact h1
        · exact h2
    _ = ((r + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) : ℝ) *
        ((residueCardinality x.1.1 : ℝ) ^ (1 - s.re)) ^ (x.2 + 1) := by
        rw [← sqrt_pow_mul_rpow _ hq s.re (x.2 + 1)]
        ring

/-- The geometric bound of a self-pair term. -/
theorem selfCoeff_mul_exp_le {r : ℕ} {T : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{u, uQ} T) {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S)
    (hPb : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (x : {v : FinitePlace F // v ∉ S} × ℕ) (σ : ℝ) :
    selfCoeff P hP x * Real.exp (-logExponent x * σ) ≤
      ((r + 1 : ℕ) : ℝ) ^ 2 * ((residueCardinality x.1.1 : ℝ) ^ (1 - σ)) ^ (x.2 + 1) := by
  have hq : (0 : ℝ) < residueCardinality x.1.1 := by
    linarith [one_lt_residueCardinality x.1.1]
  rw [exp_neg_logExponent, selfCoeff]
  have h1 := norm_powerTrace_le _ (hPb x.1.1 x.1.2) (x.2 + 1)
  have hd : (1 : ℝ) ≤ (x.2 : ℝ) + 1 := by linarith [(Nat.cast_nonneg x.2 : (0 : ℝ) ≤ x.2)]
  have hpos : 0 ≤ ((residueCardinality x.1.1 : ℝ) ^ (-σ)) ^ (x.2 + 1) := by positivity
  calc ‖P.spectralSystem.powerTrace x.1.1 _ (x.2 + 1)‖ ^ 2 / ((x.2 : ℝ) + 1) *
        ((residueCardinality x.1.1 : ℝ) ^ (-σ)) ^ (x.2 + 1)
      ≤ ‖P.spectralSystem.powerTrace x.1.1 (fun h => x.1.2 (hP h)) (x.2 + 1)‖ ^ 2 *
          ((residueCardinality x.1.1 : ℝ) ^ (-σ)) ^ (x.2 + 1) := by
        gcongr
        exact div_le_self (sq_nonneg _) hd
    _ ≤ (((r + 1 : ℕ) : ℝ) * Real.sqrt (residueCardinality x.1.1 : ℝ) ^ (x.2 + 1)) ^ 2 *
          ((residueCardinality x.1.1 : ℝ) ^ (-σ)) ^ (x.2 + 1) := by
        gcongr
        exact h1
    _ = ((r + 1 : ℕ) : ℝ) ^ 2 * ((residueCardinality x.1.1 : ℝ) ^ (1 - σ)) ^ (x.2 + 1) := by
        rw [← sqrt_pow_mul_rpow _ hq σ (x.2 + 1)]
        ring

omit [CompactSpace (AdeleQuotient F)] in
/-- A family on `{v ∉ S} × ℕ` dominated by `C (q_v ^ (1 - σ)) ^ (n + 1)` with `σ > 2` is
summable. -/
theorem summable_of_le_geometric {S : Finset (FinitePlace F)} {σ : ℝ} (hσ : 2 < σ) {C : ℝ}
    (hC : 0 ≤ C) (f : {v : FinitePlace F // v ∉ S} × ℕ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, f x ≤ C * ((residueCardinality x.1.1 : ℝ) ^ (1 - σ)) ^ (x.2 + 1)) :
    Summable f := by
  set y : {v : FinitePlace F // v ∉ S} → ℝ := fun v => (residueCardinality v.1 : ℝ) ^ (1 - σ)
    with hy
  have hy0 : ∀ v, 0 ≤ y v := fun v => Real.rpow_nonneg (by positivity) _
  have hyhalf : ∀ v, y v ≤ 1 / 2 := by
    intro v
    have hq2 : (2 : ℝ) ≤ residueCardinality v.1 := by
      exact_mod_cast CuspidalPairEulerConvergence.two_le_residueCardinality v.1
    calc y v = (residueCardinality v.1 : ℝ) ^ (1 - σ) := rfl
      _ ≤ (2 : ℝ) ^ (1 - σ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  let g : {v : FinitePlace F // v ∉ S} × ℕ → ℝ := fun x => C * y x.1 ^ (x.2 + 1)
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg hC (pow_nonneg (hy0 _) _)
  have hfib : ∀ v, HasSum (fun n : ℕ => g (v, n)) (C * y v * (1 - y v)⁻¹) := by
    intro v
    have h := (hasSum_geometric_of_lt_one (hy0 v) (by linarith [hyhalf v])).mul_left (C * y v)
    convert h using 1
    funext n
    simp only [g]
    ring
  have hrow : Summable fun v : {v : FinitePlace F // v ∉ S} => C * y v * (1 - y v)⁻¹ := by
    have hbase : Summable fun v : {v : FinitePlace F // v ∉ S} => y v := by
      have h := (HeckeEulerProduct.summable_absNorm_rpow (K := F)
        (show 1 < σ - 1 by linarith)).comp_injective
        (Subtype.val_injective (p := fun v : FinitePlace F => v ∉ S))
      refine h.congr fun v => ?_
      simp only [Function.comp_apply, hy]
      rw [CuspidalPairEulerConvergence.residueCardinality_eq_absNorm]
      congr 1
      ring
    refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) (hbase.mul_left (2 * C))
    · exact mul_nonneg (mul_nonneg hC (hy0 v)) (inv_nonneg.mpr (by linarith [hyhalf v]))
    · have h1 : (1 - y v)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith [hyhalf v]) (by norm_num)]
        linarith [hyhalf v]
      calc C * y v * (1 - y v)⁻¹ ≤ C * y v * 2 :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hC (hy0 v))
        _ = 2 * C * y v := by ring
  have hgs : Summable g := by
    refine (summable_prod_of_nonneg (fun x => hg0 x)).mpr ⟨fun v => (hfib v).summable, ?_⟩
    refine hrow.congr fun v => ?_
    exact ((hfib v).tsum_eq).symm
  exact Summable.of_nonneg_of_le hf0 hf hgs

/-- Summability on `V × ℕ` from summability away from finitely many `v` and on every fiber. -/
theorem summable_of_summable_except {V : Type*} (E : V → Prop) (hE : {v | E v}.Finite)
    (f : V × ℕ → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfib : ∀ v, Summable fun n => f (v, n))
    (hmain : Summable fun x : {v // ¬ E v} × ℕ => f (x.1.1, x.2)) : Summable f := by
  refine (summable_prod_of_nonneg (fun x => hf0 x)).mpr ⟨hfib, ?_⟩
  have h1 : Summable fun w : {v // ¬ E v} => ∑' n, f (w.1, n) :=
    ((summable_prod_of_nonneg (fun x => hf0 _)).mp hmain).2
  have h2 : Summable fun w : {v | E v} => ∑' n, f (w.1, n) := by
    have : Finite {v | E v} := hE.to_subtype
    exact Summable.of_finite
  exact (summable_subtype_and_compl (s := {v | E v})).mp ⟨h2, h1⟩

end Norms

/-! ### The product as the exponential of the double series -/

section Product

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The local logarithm at one place, for `Re s > 1`, from the bounds `q_v ^ (1/2)`. -/
theorem exists_hasSum_logEulerTerm {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPb : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (hP'b : ∀ v (hv : v ∉ S), ∀ α ∈ ((P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)) :
      Unramified.Eigenvalues (t + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (v : {v : FinitePlace F // v ∉ S}) {s : ℂ} (hs : 1 < s.re) :
    ∃ w : ℂ, HasSum (fun n : ℕ => logEulerTerm P P' hP hP' v n s) w ∧
      partialEulerFactor P P' hP hP' v s = Complex.exp w := by
  have hq1 := one_lt_residueCardinality v.1
  have hq : (0 : ℝ) < residueCardinality v.1 := by linarith
  have hbound : ∀ α ∈ ((P.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ∀ β ∈ ((P'.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP' h)) :
        Unramified.Eigenvalues (t + 1)) : Multiset ℂˣ),
      ‖(α : ℂ) * β * RankinSelberg.spectralPoint (residueCardinality v.1) s‖ < 1 := by
    intro α hα β hβ
    rw [norm_mul, norm_mul, CuspidalPairEulerConvergence.norm_spectralPoint]
    have h1 := hPb v.1 v.2 α hα
    have h2 := hP'b v.1 v.2 β hβ
    calc ‖(α : ℂ)‖ * ‖(β : ℂ)‖ * (residueCardinality v.1 : ℝ) ^ (-s.re)
        ≤ Real.sqrt (residueCardinality v.1 : ℝ) * Real.sqrt (residueCardinality v.1 : ℝ) *
            (residueCardinality v.1 : ℝ) ^ (-s.re) := by
          gcongr
      _ = (residueCardinality v.1 : ℝ) ^ (1 - s.re) := by
          rw [Real.mul_self_sqrt hq.le, show (1 : ℝ) - s.re = 1 + -s.re by ring,
            Real.rpow_add hq, Real.rpow_one]
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  obtain ⟨w, hw, he⟩ := exists_hasSum_pairLog _ _ _ hbound
  exact ⟨w, hw, he⟩

/-- **The product (Jacquet–Shalika I, (5.3.2)).** If the double series converges
absolutely at `s` with `Re s > 1`, the partial Euler product converges absolutely and
unconditionally to the exponential of its sum. -/
theorem summable_and_hasProd_of_summable {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPb : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    (hP'b : ∀ v (hv : v ∉ S), ∀ α ∈ ((P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)) :
      Unramified.Eigenvalues (t + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ))
    {s : ℂ} (hs : 1 < s.re)
    (hsum : Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
      ‖logEulerTerm P P' hP hP' x.1 x.2 s‖) :
    Summable (fun v => ‖partialEulerFactor P P' hP hP' v s - 1‖) ∧
      HasProd (fun v => partialEulerFactor P P' hP hP' v s)
        (Complex.exp (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
          logEulerTerm P P' hP hP' x.1 x.2 s)) := by
  choose w hw he using fun v => exists_hasSum_logEulerTerm P P' hP hP' hPb hP'b v hs
  have hsum' : Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
      logEulerTerm P P' hP hP' x.1 x.2 s := hsum.of_norm
  have hfib : HasSum w (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
      logEulerTerm P P' hP hP' x.1 x.2 s) :=
    hsum'.hasSum.prod_fiberwise fun v => hw v
  have hprod : HasProd (fun v => partialEulerFactor P P' hP hP' v s)
      (Complex.exp (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
        logEulerTerm P P' hP hP' x.1 x.2 s)) := by
    have h := hfib.cexp
    have e : (Complex.exp ∘ w) = fun v => partialEulerFactor P P' hP hP' v s :=
      funext fun v => (he v).symm
    rw [e] at h
    exact h
  refine ⟨?_, hprod⟩
  have hN := (summable_prod_of_nonneg (fun x => norm_nonneg _)).mp hsum
  have hwle : ∀ v, ‖w v‖ ≤ ∑' n, ‖logEulerTerm P P' hP hP' v n s‖ := by
    intro v
    rw [← (hw v).tsum_eq]
    exact norm_tsum_le_tsum_norm (hN.1 v)
  have hev : ∀ᶠ v in Filter.cofinite, ∑' n, ‖logEulerTerm P P' hP hP' v n s‖ ≤ 1 :=
    hN.2.tendsto_cofinite_zero.eventually (eventually_le_nhds one_pos)
  refine Summable.of_norm_bounded_eventually (hN.2.mul_left 2) ?_
  filter_upwards [hev] with v hv
  rw [norm_norm, he v]
  calc ‖Complex.exp (w v) - 1‖ ≤ 2 * ‖w v‖ := Complex.norm_exp_sub_one_le ((hwle v).trans hv)
    _ ≤ 2 * ∑' n, ‖logEulerTerm P P' hP hP' v n s‖ := by
        gcongr
        exact hwle v

end Product

/-! ### The self-pair and Landau's theorem -/

section SelfPair

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The places outside `S` and outside `E`, as places outside `S ∪ E`. -/
def exceptEquiv [DecidableEq (FinitePlace F)] (S E : Finset (FinitePlace F)) :
    {w : {v : FinitePlace F // v ∉ S} // w.1 ∉ E} ≃ {v : FinitePlace F // v ∉ S ∪ E} where
  toFun w := ⟨w.1.1, fun h => (Finset.mem_union.mp h).elim w.1.2 w.2⟩
  invFun v := ⟨⟨v.1, fun h => v.2 (Finset.mem_union_left _ h)⟩,
    fun h => v.2 (Finset.mem_union_right _ h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For a contragredient presentation, the self-pair term is a term of a general Dirichlet
series with the nonnegative coefficient `|tr A_v ^ (n + 1)|² / (n + 1)`. -/
theorem logEulerTerm_self_eq {r : ℕ} {T Td : CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T) (hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    {S S' : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hPS' : P.exceptional ⊆ S')
    (hPdS' : Pd.exceptional ⊆ S') (v : FinitePlace F) (hvS : v ∉ S) (hvS' : v ∉ S')
    (n : ℕ) (s : ℂ) :
    logEulerTerm P Pd hPS' hPdS' ⟨v, hvS'⟩ n s =
      GeneralDirichlet.term (selfCoeff P hP) logExponent (⟨v, hvS⟩, n) s := by
  have hc := eigenvalues_eq_conjSpectrum hT hTd P Pd v (fun h => hvS (hP h))
    (fun h => hvS' (hPdS' h))
  have hpt : Pd.spectralSystem.powerTrace v (fun h => hvS' (hPdS' h)) (n + 1) =
      starRingEnd ℂ (P.spectralSystem.powerTrace v (fun h => hvS (hP h)) (n + 1)) := by
    change (Pd.spectralSystem.eigenvalues v _).powerTrace (n + 1) =
      starRingEnd ℂ ((P.spectralSystem.eigenvalues v _).powerTrace (n + 1))
    rw [hc, Unramified.powerTrace_conjSpectrum]
  have hX : RankinSelberg.spectralPoint (residueCardinality v) s ^ (n + 1) =
      Complex.exp (-((logExponent (S := S) (⟨v, hvS⟩, n) : ℝ) : ℂ) * s) :=
    spectralPoint_pow_eq_exp (⟨v, hvS⟩, n) s
  unfold logEulerTerm GeneralDirichlet.term
  change P.spectralSystem.powerTrace v (fun h => hvS (hP h)) (n + 1) *
      Pd.spectralSystem.powerTrace v (fun h => hvS' (hPdS' h)) (n + 1) *
      RankinSelberg.spectralPoint (residueCardinality v) s ^ (n + 1) / ((n : ℂ) + 1) =
    ((‖P.spectralSystem.powerTrace v (fun h => hvS (hP h)) (n + 1)‖ ^ 2 / ((n : ℝ) + 1) : ℝ) :
        ℂ) * Complex.exp (-((logExponent (S := S) (⟨v, hvS⟩, n) : ℝ) : ℂ) * s)
  rw [hpt, Complex.mul_conj, Complex.normSq_eq_norm_sq, hX]
  push_cast
  ring

theorem norm_conjSpectrum_le {n : ℕ} (a : Unramified.Eigenvalues n) {B : ℝ}
    (hB : ∀ α ∈ (a : Multiset ℂˣ), ‖(α : ℂ)‖ ≤ B) :
    ∀ β ∈ ((Unramified.conjSpectrum a : Unramified.Eigenvalues n) : Multiset ℂˣ),
      ‖(β : ℂ)‖ ≤ B := by
  intro β hβ
  rw [Unramified.coe_conjSpectrum] at hβ
  obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hβ
  rw [Units.coe_map]
  change ‖starRingEnd ℂ (α : ℂ)‖ ≤ B
  rw [Complex.norm_conj]
  exact hB α hα

/-- **Landau's theorem for the self-pair (Jacquet–Shalika I, (5.3.3)).** Given Lemma (5.2),
the series `∑ |tr A_v ^ (n + 1)|² q_v ^ (-(n + 1) σ) / (n + 1)` converges for every
`σ > 1`. -/
theorem summableAt_selfCoeff (h52 : CuspidalSelfPairContinuationStatement.{u, uQ}) {r : ℕ}
    {T : CuspidalOperatorRealization F r} (hT : HasUnitaryCentralCharacter T)
    (P : CuspidalSpectralPresentation.{u, uQ} T) {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) {σ : ℝ} (hσ : 1 < σ) :
    GeneralDirichlet.SummableAt (selfCoeff P hP) logExponent σ := by
  classical
  obtain ⟨Td, hTd⟩ := Automorphic.cuspidalContragredientExistence.{u} F r T
  obtain ⟨Pd⟩ := Automorphic.cuspidalDualPresentationExistence.{u, uQ, uQ} F r T Td hTd P
  have hPS' : P.exceptional ⊆ S ∪ Pd.exceptional := hP.trans Finset.subset_union_left
  have hPdS' : Pd.exceptional ⊆ S ∪ Pd.exceptional := Finset.subset_union_right
  obtain ⟨L, hLd, σs, hL⟩ := h52 F r T Td hT hTd P Pd (S ∪ Pd.exceptional) hPS' hPdS'
  have hPb : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) :=
    fun v _ _ hα => norm_eigenvalue_le_sqrt hT P v _ hα
  have hPb' : ∀ v (hv : v ∉ S ∪ Pd.exceptional), ∀ α ∈
      ((P.spectralSystem.eigenvalues v (fun h => hv (hPS' h)) :
        Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) :=
    fun v _ _ hα => norm_eigenvalue_le_sqrt hT P v _ hα
  have hPdb : ∀ v (hv : v ∉ S ∪ Pd.exceptional), ∀ α ∈
      ((Pd.spectralSystem.eigenvalues v (fun h => hv (hPdS' h)) :
        Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) := by
    intro v hv α hα
    have hc := eigenvalues_eq_conjSpectrum hT hTd P Pd v (fun h => hv (hPS' h))
      (fun h => hv (hPdS' h))
    have hα' := (congrArg (fun e : Unramified.Eigenvalues (r + 1) => α ∈ (e : Multiset ℂˣ))
      hc).mp hα
    exact norm_conjSpectrum_le _ (fun β hβ => norm_eigenvalue_le_sqrt hT P v _ hβ) α hα'
  let emb : {w : {v : FinitePlace F // v ∉ S} // w.1 ∉ Pd.exceptional} × ℕ →
      {v : FinitePlace F // v ∉ S} × ℕ := fun x => (x.1.1, x.2)
  have hemb : Function.Injective emb := by
    rintro ⟨⟨w, hw⟩, n⟩ ⟨⟨w', hw'⟩, n'⟩ h
    simp only [emb, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  let c' : {w : {v : FinitePlace F // v ∉ S} // w.1 ∉ Pd.exceptional} × ℕ → ℝ :=
    fun x => selfCoeff P hP (emb x)
  let ℓ' : {w : {v : FinitePlace F // v ∉ S} // w.1 ∉ Pd.exceptional} × ℕ → ℝ :=
    fun x => logExponent (emb x)
  have hσ₁2 : 2 < max σs 2 + 1 := by linarith [le_max_right σs 2]
  have h₁ : GeneralDirichlet.SummableAt c' ℓ' (max σs 2 + 1) := by
    have hbig : Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
        selfCoeff P hP x * Real.exp (-logExponent x * (max σs 2 + 1)) :=
      summable_of_le_geometric hσ₁2 (sq_nonneg _) _
        (fun x => mul_nonneg (selfCoeff_nonneg P hP x) (Real.exp_pos _).le)
        (fun x => selfCoeff_mul_exp_le P hP hPb x _)
    exact hbig.comp_injective hemb
  have hLD : ∀ s : ℂ, max σs 2 + 1 < s.re →
      L s = Complex.exp (GeneralDirichlet.series c' ℓ' s) := by
    intro s hs
    have hs1 : σs < s.re := by linarith [le_max_left σs 2]
    have hs2 : 2 < s.re := by linarith
    obtain ⟨-, hprod⟩ := hL s hs1
    have hsum : Summable fun x : {v : FinitePlace F // v ∉ S ∪ Pd.exceptional} × ℕ =>
        ‖logEulerTerm P Pd hPS' hPdS' x.1 x.2 s‖ :=
      summable_of_le_geometric hs2 (by positivity) _ (fun x => norm_nonneg _)
        (fun x => norm_logEulerTerm_le P Pd hPS' hPdS' hPb' hPdb x s)
    obtain ⟨-, hprod2⟩ := summable_and_hasProd_of_summable P Pd hPS' hPdS' hPb' hPdb
      (by linarith) hsum
    rw [hprod.unique hprod2]
    congr 1
    rw [GeneralDirichlet.series,
      ← ((exceptEquiv S Pd.exceptional).prodCongr (Equiv.refl ℕ)).tsum_eq]
    refine tsum_congr fun x => ?_
    exact logEulerTerm_self_eq hT hTd P Pd hP hPS' hPdS' x.1.1.1 x.1.1.2 _ x.2 s
  have hland := GeneralDirichlet.summableAt_of_exp (c := c') (ℓ := ℓ')
    (fun x => selfCoeff_nonneg P hP _) (Real.log_pos one_lt_two)
    (fun x => log_two_le_logExponent _) h₁ hLd hLD σ hσ
  refine summable_of_summable_except (fun w : {v : FinitePlace F // v ∉ S} =>
    w.1 ∈ Pd.exceptional) ?_ _
    (fun x => mul_nonneg (selfCoeff_nonneg P hP x) (Real.exp_pos _).le) (fun v => ?_) hland
  · exact (Finset.finite_toSet _).preimage Subtype.val_injective.injOn
  · have hq1 := one_lt_residueCardinality v.1
    set y := (residueCardinality v.1 : ℝ) ^ (1 - σ) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg (by linarith) _
    have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (selfCoeff_nonneg P hP _)
      (Real.exp_pos _).le) (fun n => selfCoeff_mul_exp_le P hP hPb (v, n) σ) ?_
    have h := (summable_geometric_of_lt_one hy0 hy1).mul_left (((r + 1 : ℕ) : ℝ) ^ 2 * y)
    refine h.congr fun n => ?_
    simp only [hy]
    ring

end SelfPair

/-! ### Theorem (5.3) -/

section Theorem

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

theorem half_bound (a b d e : ℝ) (hd : 0 < d) (he : 0 ≤ e) :
    a * b / d * e ≤ 1 / 2 * (a ^ 2 / d * e + b ^ 2 / d * e) := by
  have key : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have hed : 0 ≤ e / d := div_nonneg he hd.le
  calc a * b / d * e = (a * b) * (e / d) := by ring
    _ ≤ ((a ^ 2 + b ^ 2) / 2) * (e / d) := mul_le_mul_of_nonneg_right key hed
    _ = 1 / 2 * (a ^ 2 / d * e + b ^ 2 / d * e) := by ring

end Theorem

end CuspidalPairAbsoluteConvergence

open CuspidalPairAbsoluteConvergence

/-- **Jacquet–Shalika (1981), I, Theorem (5.3), from Lemma (5.2).** -/
theorem cuspidalPairAbsoluteConvergence_of_selfPairContinuation
    (h52 : CuspidalSelfPairContinuationStatement.{u, uQ}) :
    CuspidalPairAbsoluteConvergenceStatement.{u, uQ} := by
  intro F _ _ _ r t T T' hT hT' P P' S hP hP' s hs
  have hA := summableAt_selfCoeff h52 hT P hP hs
  have hB := summableAt_selfCoeff h52 hT' P' hP' hs
  have hPb : ∀ v (hv : v ∉ S), ∀ α ∈ ((P.spectralSystem.eigenvalues v (fun h => hv (hP h)) :
      Unramified.Eigenvalues (r + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) :=
    fun v _ _ hα => norm_eigenvalue_le_sqrt hT P v _ hα
  have hP'b : ∀ v (hv : v ∉ S), ∀ α ∈ ((P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)) :
      Unramified.Eigenvalues (t + 1)) : Multiset ℂˣ),
      ‖(α : ℂ)‖ ≤ Real.sqrt (residueCardinality v : ℝ) :=
    fun v _ _ hα => norm_eigenvalue_le_sqrt hT' P' v _ hα
  have h1 : Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
      ‖logEulerTerm P P' hP hP' x.1 x.2 s‖ := by
    refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
      ((hA.add hB).mul_left (1 / 2))
    rw [norm_logEulerTerm]
    exact half_bound _ _ _ _ (by positivity) (Real.exp_pos _).le
  obtain ⟨h2, h3⟩ := summable_and_hasProd_of_summable P P' hP hP' hPb hP'b hs h1
  exact ⟨h1, h2, h3⟩

/-- **The reduction `CuspidalPairAbsoluteConvergenceReductionStatement`**: Lemma (5.2) implies
Theorem (5.3), at the same universes. -/
theorem cuspidalPairAbsoluteConvergenceReduction :
    CuspidalPairAbsoluteConvergenceReductionStatement.{u, uQ} :=
  cuspidalPairAbsoluteConvergence_of_selfPairContinuation

end Langlands.Global
