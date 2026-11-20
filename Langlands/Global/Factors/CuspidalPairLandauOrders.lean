import Langlands.Global.Factors.SpectralSquarePoles
import Langlands.Automorphic.CuspidalContragredientPresentationExistenceProof
import Langlands.Global.Factors.CuspidalPairPartialContinuation
import Langlands.Global.Factors.CuspidalNormPowerTwist
import Langlands.Global.Factors.CuspidalPairLogSeries
import Langlands.Analysis.LogarithmicAsymptotics

/-! # Exact boundary orders from positivity of squared traces -/

noncomputable section

set_option autoImplicit false

universe u uQ

open Filter Topology
open scoped ComplexConjugate

namespace Langlands.Global.CuspidalPairLandauOrders

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open Unramified (Eigenvalues conjSpectrum)
open GeneralDirichlet (SummableAt term series)
open CuspidalPairFunctionalEquation (residueCardinality HasIrreducibleAdmissibleComponents
  pairEulerPolynomial)
open CuspidalPairAbsoluteConvergence
open CuspidalPairBoundaryNonvanishing (IsPartialPairLFunction)
open CuspidalPairPoles (IsTrivialOnSplitCentre)
open CuspidalPairPartialContinuation (PartialPairContinuationAt)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type u} [Field F] [NumberField F]

private abbrev PlaceOutside (S : Finset (FinitePlace F)) :=
  {v : FinitePlace F // v ∉ S}

private abbrev LogIndex (S : Finset (FinitePlace F)) := PlaceOutside S × ℕ

private def conjugateFamily {S : Finset (FinitePlace F)} {n : ℕ}
    (A : PlaceOutside S → Eigenvalues n) : PlaceOutside S → Eigenvalues n :=
  fun v => conjSpectrum (A v)

private theorem exists_eigenvalue_norm_ge_one {n : ℕ} (hn : 0 < n) (A : Eigenvalues n)
    (h : conjSpectrum A = A.map Inv.inv) :
    ∃ a ∈ (A : Multiset ℂˣ), 1 ≤ ‖(a : ℂ)‖ := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (s := (A : Multiset ℂˣ)) (by
    intro hz
    have hc : Multiset.card (A : Multiset ℂˣ) = n := Sym.card_coe
    rw [hz, Multiset.card_zero] at hc
    omega)
  by_cases ha1 : 1 ≤ ‖(a : ℂ)‖
  · exact ⟨a, ha, ha1⟩
  have hai : a⁻¹ ∈ (conjSpectrum A : Multiset ℂˣ) := by
    rw [h, Sym.coe_map]
    exact Multiset.mem_map.mpr ⟨a, ha, rfl⟩
  rw [Unramified.coe_conjSpectrum] at hai
  obtain ⟨b, hb, hab⟩ := Multiset.mem_map.mp hai
  have hnorm := congrArg (fun c : ℂˣ => ‖(c : ℂ)‖) hab
  simp only [Units.coe_map, Units.val_inv_eq_inv_val, norm_inv] at hnorm
  change ‖conj (b : ℂ)‖ = ‖(a : ℂ)‖⁻¹ at hnorm
  rw [Complex.norm_conj] at hnorm
  refine ⟨b, hb, ?_⟩
  rw [hnorm]
  exact (one_le_inv₀ (norm_pos_iff.mpr a.ne_zero)).mpr (le_of_not_ge ha1)

private def pairTerm {S : Finset (FinitePlace F)} {n m : ℕ}
    (A : PlaceOutside S → Eigenvalues n) (B : PlaceOutside S → Eigenvalues m)
    (x : LogIndex S) (s : ℂ) : ℂ :=
  (A x.1).powerTrace (x.2 + 1) * (B x.1).powerTrace (x.2 + 1) *
    Complex.exp (-(logExponent x : ℂ) * s) / ((x.2 : ℂ) + 1)

private def phase (v : FinitePlace F) (θ : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp ((Real.log (residueCardinality v : ℝ) : ℂ) * (θ * Complex.I)))
    (Complex.exp_ne_zero _)

private def combinedSpectrum {S : Finset (FinitePlace F)} {n m : ℕ}
    (A : PlaceOutside S → Eigenvalues n) (B : PlaceOutside S → Eigenvalues m) (θ : ℝ)
    (v : PlaceOutside S) : Eigenvalues (n + m) :=
  (A v).directSum ((conjSpectrum (B v)).scale (phase v.1 θ))

private theorem combinedSpectrum_has_large_eigenvalue
    {S : Finset (FinitePlace F)} {n m : ℕ} {A : PlaceOutside S → Eigenvalues n}
    (B : PlaceOutside S → Eigenvalues m) (θ : ℝ)
    (hA : ∀ v, ∃ a ∈ (A v : Multiset ℂˣ), 1 ≤ ‖(a : ℂ)‖) :
    ∀ v, ∃ a ∈ (combinedSpectrum A B θ v : Multiset ℂˣ), 1 ≤ ‖(a : ℂ)‖ := by
  intro v
  obtain ⟨a, ha, ha1⟩ := hA v
  refine ⟨a, ?_, ha1⟩
  simp only [combinedSpectrum, Eigenvalues.directSum, Sym.coe_append, Multiset.mem_add]
  exact .inl ha

private theorem conj_imaginaryShift (θ : ℝ) :
    conj ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

private theorem phase_pow {S : Finset (FinitePlace F)} (x : LogIndex S) (θ : ℝ) :
    (phase x.1.1 θ : ℂ) ^ (x.2 + 1) =
      Complex.exp ((logExponent x : ℂ) * (θ * Complex.I)) := by
  simp only [phase, Units.val_mk0, ← Complex.exp_nat_mul, logExponent]
  push_cast
  ring_nf

private theorem pairTerm_add {S : Finset (FinitePlace F)} {n m : ℕ}
    (A : PlaceOutside S → Eigenvalues n) (B : PlaceOutside S → Eigenvalues m)
    (x : LogIndex S) (s w : ℂ) :
    pairTerm A B x (s + w) = pairTerm A B x s * Complex.exp (-(logExponent x : ℂ) * w) := by
  simp only [pairTerm, mul_add, Complex.exp_add]
  ring

private theorem pairTerm_conjugate {S : Finset (FinitePlace F)} {n m : ℕ}
    (A : PlaceOutside S → Eigenvalues n) (B : PlaceOutside S → Eigenvalues m)
    (x : LogIndex S) (s : ℂ) :
    pairTerm (conjugateFamily A) (conjugateFamily B) x (conj s) = conj (pairTerm A B x s) := by
  simp [pairTerm, conjugateFamily, Unramified.powerTrace_conjSpectrum, map_mul, ← Complex.exp_conj]

private theorem square_expansion (a b c : ℂ) (hc : c * conj c = 1) :
    ((‖a + c * conj b‖ ^ 2 : ℝ) : ℂ) =
      a * conj a + b * conj b + a * b * conj c + conj a * conj b * c := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [map_add, map_mul, starRingEnd_self_apply]
  linear_combination (b * conj b) * hc

private theorem mixed_square_term {S : Finset (FinitePlace F)} {n m : ℕ}
    (A : PlaceOutside S → Eigenvalues n) (B : PlaceOutside S → Eigenvalues m)
    (x : LogIndex S) (s : ℂ) (θ : ℝ) :
    term (SpectralSquare.coeff (combinedSpectrum A B θ)) logExponent x s =
      pairTerm A (conjugateFamily A) x s + pairTerm B (conjugateFamily B) x s +
        (pairTerm A B x (s + θ * Complex.I) +
          pairTerm (conjugateFamily A) (conjugateFamily B) x (s - θ * Complex.I)) := by
  have hconj : conj (Complex.exp ((logExponent x : ℂ) * (θ * Complex.I))) =
      Complex.exp (-(logExponent x : ℂ) * (θ * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, conj_imaginaryShift, mul_neg, neg_mul]
  have hnorm : Complex.exp ((logExponent x : ℂ) * (θ * Complex.I)) *
      conj (Complex.exp ((logExponent x : ℂ) * (θ * Complex.I))) = 1 := by
    rw [hconj, neg_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [sub_eq_add_neg, pairTerm_add, pairTerm_add,
    show -(logExponent x : ℂ) * -(θ * Complex.I) =
        (logExponent x : ℂ) * (θ * Complex.I) by ring, ← hconj]
  simp only [term, SpectralSquare.coeff, combinedSpectrum, Eigenvalues.powerTrace_directSum,
    Eigenvalues.powerTrace_scale, Unramified.powerTrace_conjSpectrum, phase_pow]
  rw [Complex.ofReal_div, square_expansion _ _ _ hnorm]
  push_cast
  simp only [pairTerm, conjugateFamily, Unramified.powerTrace_conjSpectrum]
  ring

private theorem self_square_term {S : Finset (FinitePlace F)} {n : ℕ}
    (A : PlaceOutside S → Eigenvalues n) (x : LogIndex S) (s : ℂ) :
    pairTerm (conjugateFamily A) A x s = term (SpectralSquare.coeff A) logExponent x s := by
  simp only [pairTerm, conjugateFamily, Unramified.powerTrace_conjSpectrum, term, SpectralSquare.coeff]
  rw [Complex.ofReal_div, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  push_cast
  ring

section Presentations

variable [CompactSpace (AdeleQuotient F)]
variable {r t : ℕ} {T Td : CuspidalOperatorRealization F r} {U : CuspidalOperatorRealization F t}

private def spectra {S : Finset (FinitePlace F)} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hP : P.exceptional ⊆ S) (v : PlaceOutside S) : Eigenvalues (r + 1) :=
  P.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP h))

private theorem logEulerTerm_eq_pairTerm {S : Finset (FinitePlace F)}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Q : CuspidalSpectralPresentation.{u, uQ} U)
    (hP : P.exceptional ⊆ S) (hQ : Q.exceptional ⊆ S) (x : LogIndex S) (s : ℂ) :
    logEulerTerm P Q hP hQ x.1 x.2 s = pairTerm (spectra P hP) (spectra Q hQ) x s := by
  unfold logEulerTerm pairTerm spectra
  rw [spectralPoint_pow_eq_exp x]
  rfl

private theorem conjugateFamily_spectra {S : Finset (FinitePlace F)}
    (hT : HasUnitaryCentralCharacter T)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Pc : CuspidalSpectralPresentation.{u, uQ} Td)
    (hP : P.exceptional ⊆ S) (hPc : Pc.exceptional ⊆ S)
    (hd : Td.realization.IsContragredientOf T.realization) :
    conjugateFamily (spectra P hP) = spectra Pc hPc := by
  funext v
  exact (eigenvalues_eq_conjSpectrum hT hd P Pc v.1 (fun h => v.2 (hP h))
    (fun h => v.2 (hPc h))).symm

private theorem spectra_has_large_eigenvalue {S : Finset (FinitePlace F)}
    (hT : HasUnitaryCentralCharacter T)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Pc : CuspidalSpectralPresentation.{u, uQ} Td)
    (hP : P.exceptional ⊆ S) (hPc : Pc.exceptional ⊆ S)
    (hd : Td.realization.IsContragredientOf T.realization) :
    ∀ v, ∃ a ∈ (spectra P hP v : Multiset ℂˣ), 1 ≤ ‖(a : ℂ)‖ := by
  intro v
  apply exists_eigenvalue_norm_ge_one (Nat.succ_pos r)
  have hc := congrFun (conjugateFamily_spectra hT P Pc hP hPc hd) v
  change conjSpectrum (spectra P hP v) = spectra Pc hPc v at hc
  rw [hc]
  exact CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf
    T Td P Pc hd v.1 _ _

private structure ContinuedPair {S : Finset (FinitePlace F)}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Q : CuspidalSpectralPresentation.{u, uQ} U)
    (hP : P.exceptional ⊆ S) (hQ : Q.exceptional ⊆ S) where
  L : ℂ → ℂ
  exp_eq (s : ℂ) (hs : 1 < s.re) :
    L s = Complex.exp (∑' x : LogIndex S, logEulerTerm P Q hP hQ x.1 x.2 s)
  euler : IsPartialPairLFunction P Q hP hQ L
  analytic (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) : AnalyticAt ℂ L s
  order_ge_neg_one : -1 ≤ meromorphicOrderAt L 1
  order_nonneg_of_nondual :
    (¬ ∃ hrt : r = t,
      OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) U.realization) →
    0 ≤ meromorphicOrderAt L 1

private theorem continuedPair_exists (hcont : PartialPairContinuationAt.{u, uQ} F)
    (hT : HasUnitaryCentralCharacter T) (hU : HasUnitaryCentralCharacter U)
    (hTs : IsTrivialOnSplitCentre T) (hUs : IsTrivialOnSplitCentre U)
    {S : Finset (FinitePlace F)}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Q : CuspidalSpectralPresentation.{u, uQ} U)
    (hPa : HasIrreducibleAdmissibleComponents P) (hQa : HasIrreducibleAdmissibleComponents Q)
    (hP : P.exceptional ⊆ S) (hQ : Q.exceptional ⊆ S) :
    Nonempty (ContinuedPair P Q hP hQ) := by
  obtain ⟨L, hExp, hEuler, hAn, hPole, hDual, -⟩ :=
    hcont r t T U hT hU hTs hUs P Q hPa hQa S hP hQ
  exact ⟨⟨L, hExp, hEuler, hAn, hPole, hDual⟩⟩

private theorem ContinuedPair.exp_eq_pairTerm {S : Finset (FinitePlace F)}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {Q : CuspidalSpectralPresentation.{u, uQ} U}
    {hP : P.exceptional ⊆ S} {hQ : Q.exceptional ⊆ S}
    (D : ContinuedPair P Q hP hQ) (s : ℂ) (hs : 1 < s.re) :
    D.L s = Complex.exp (∑' x : LogIndex S, pairTerm (spectra P hP) (spectra Q hQ) x s) :=
  (D.exp_eq s hs).trans
    (congrArg Complex.exp (tsum_congr fun x => logEulerTerm_eq_pairTerm P Q hP hQ x s))

private theorem summable_norm_pairTerm (hconv : CuspidalPairAbsoluteConvergenceStatement.{u, uQ})
    (hT : HasUnitaryCentralCharacter T) (hU : HasUnitaryCentralCharacter U)
    {S : Finset (FinitePlace F)}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (Q : CuspidalSpectralPresentation.{u, uQ} U)
    (hP : P.exceptional ⊆ S) (hQ : Q.exceptional ⊆ S) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun x : LogIndex S => ‖pairTerm (spectra P hP) (spectra Q hQ) x s‖) :=
  (hconv F r t T U hT hU P Q S hP hQ s hs).1.congr fun x =>
    congrArg norm (logEulerTerm_eq_pairTerm P Q hP hQ x s)

private theorem order_eq_neg_one {k : WithTop ℤ} (ha : -1 ≤ k) (hb : k < 0) : k = -1 := by
  cases k with
  | top => exact absurd hb (not_lt.mpr le_top)
  | coe k =>
    have ha' : (-1 : ℤ) ≤ k := WithTop.coe_le_coe.mp ha
    have hb' : k < (0 : ℤ) := WithTop.coe_lt_coe.mp hb
    exact congrArg WithTop.some (show k = -1 by omega)

private theorem order_self (hconv : CuspidalPairAbsoluteConvergenceStatement.{u, uQ})
    (hT : HasUnitaryCentralCharacter T) (hTd : HasUnitaryCentralCharacter Td)
    (hd : Td.realization.IsContragredientOf T.realization)
    {S : Finset (FinitePlace F)}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
    {hP : P.exceptional ⊆ S} {hPd : Pd.exceptional ⊆ S}
    (D : ContinuedPair Pd P hPd hP) :
    meromorphicOrderAt D.L 1 = -1 := by
  let A := spectra P hP
  have hAc : spectra Pd hPd = conjugateFamily A := (conjugateFamily_spectra hT P Pd hP hPd hd).symm
  have hterm (x : LogIndex S) (s : ℂ) :
      pairTerm (spectra Pd hPd) A x s = term (SpectralSquare.coeff A) logExponent x s := by
    rw [hAc, self_square_term]
  have hsum : SummableAt (SpectralSquare.coeff A) logExponent 2 := by
    refine (summable_norm_pairTerm hconv hTd hT Pd P hPd hP 2 (by norm_num)).congr fun x => ?_
    rw [hterm, GeneralDirichlet.norm_term, abs_of_nonneg (SpectralSquare.coeff_nonneg A x)]
    norm_num
  have hexp (s : ℂ) (hs : 2 < s.re) :
      D.L s = Complex.exp (series (SpectralSquare.coeff A) logExponent s) :=
    (D.exp_eq_pairTerm s (one_lt_two.trans hs)).trans (congrArg Complex.exp (tsum_congr fun x => hterm x s))
  have horder (σ : ℝ) (hσ : 0 < σ) (h1 : σ ≠ 1) : 0 ≤ meromorphicOrderAt D.L (σ : ℂ) :=
    (D.analytic σ (Complex.ofReal_ne_zero.mpr hσ.ne') (by simpa using h1)).meromorphicOrderAt_nonneg
  exact order_eq_neg_one D.order_ge_neg_one
    (SpectralSquare.poleDetection F S _ (Nat.succ_pos r) A
      (spectra_has_large_eigenvalue hT P Pd hP hPd hd) hsum
      (fun z _ => D.euler.1 z (Set.mem_univ z)) hexp horder)

private theorem re_add_shift (s : ℂ) (θ : ℝ) : (s + θ * Complex.I).re = s.re := by
  simp [Complex.add_re]

private theorem re_sub_shift (s : ℂ) (θ : ℝ) : (s - θ * Complex.I).re = s.re := by
  simp [Complex.sub_re]

private theorem order_nonneg_real_add {L : ℂ → ℂ} (h : ∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ L z)
    {c : ℂ} (hc : c.re = 0) (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≠ 1) :
    0 ≤ meromorphicOrderAt (fun s => L (s + c)) (σ : ℂ) := by
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  apply (h _ ?_ ?_).meromorphicOrderAt_nonneg
  · intro h0
    have hr := congrArg Complex.re h0
    simp [Complex.add_re, hc] at hr
    exact hσ.ne' hr
  · intro h1
    have hr := congrArg Complex.re h1
    simp [Complex.add_re, hc] at hr
    exact hσ₁ hr

private theorem order_nonneg_boundary {S : Finset (FinitePlace F)}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {Q : CuspidalSpectralPresentation.{u, uQ} U}
    {hP : P.exceptional ⊆ S} {hQ : Q.exceptional ⊆ S}
    (D : ContinuedPair P Q hP hQ) (θ : ℝ)
    (h : ¬ (θ = 0 ∧ ∃ hrt : r = t,
      OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) U.realization)) :
    0 ≤ meromorphicOrderAt D.L (1 + θ * Complex.I) := by
  by_cases hθ : θ = 0
  · simpa [hθ] using D.order_nonneg_of_nondual (fun hd => h ⟨hθ, hd⟩)
  · apply (D.analytic _ ?_ ?_).meromorphicOrderAt_nonneg
    · intro hz
      have hr := congrArg Complex.re hz
      rw [re_add_shift, Complex.one_re, Complex.zero_re] at hr
      norm_num at hr
    · intro hz
      have hi := congrArg Complex.im hz
      exact hθ (by simpa [Complex.add_im, Complex.mul_I_im] using hi)

private theorem order_cross (hconv : CuspidalPairAbsoluteConvergenceStatement.{u, uQ})
    (hT : HasUnitaryCentralCharacter T) (hU : HasUnitaryCentralCharacter U)
    (hTc : T.conjugate.realization.IsContragredientOf T.realization)
    (hUc : U.conjugate.realization.IsContragredientOf U.realization)
    {S : Finset (FinitePlace F)}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {Q : CuspidalSpectralPresentation.{u, uQ} U}
    {Pc : CuspidalSpectralPresentation.{u, uQ} T.conjugate}
    {Qc : CuspidalSpectralPresentation.{u, uQ} U.conjugate}
    {hP : P.exceptional ⊆ S} {hQ : Q.exceptional ⊆ S}
    {hPc : Pc.exceptional ⊆ S} {hQc : Qc.exceptional ⊆ S}
    (D₁ : ContinuedPair P Pc hP hPc) (D₂ : ContinuedPair Q Qc hQ hQc)
    (D₃ : ContinuedPair P Q hP hQ) (D₄ : ContinuedPair Pc Qc hPc hQc)
    (θ : ℝ) (hord : 0 ≤ meromorphicOrderAt D₃.L (1 + θ * Complex.I)) :
    meromorphicOrderAt D₃.L (1 + θ * Complex.I) = 0 := by
  let A := spectra P hP
  let B := spectra Q hQ
  let Ac := spectra Pc hPc
  let Bc := spectra Qc hQc
  have hAc : conjugateFamily A = Ac := conjugateFamily_spectra hT P Pc hP hPc hTc
  have hBc : conjugateFamily B = Bc := conjugateFamily_spectra hU Q Qc hQ hQc hUc
  let W := combinedSpectrum A B θ
  let f₁ (x : LogIndex S) (s : ℂ) := pairTerm A Ac x s
  let f₂ (x : LogIndex S) (s : ℂ) := pairTerm B Bc x s
  let f₃ (x : LogIndex S) (s : ℂ) := pairTerm A B x (s + θ * Complex.I)
  let f₄ (x : LogIndex S) (s : ℂ) := pairTerm Ac Bc x (s - θ * Complex.I)
  have hterm (x : LogIndex S) (s : ℂ) :
      term (SpectralSquare.coeff W) logExponent x s = f₁ x s + f₂ x s + (f₃ x s + f₄ x s) := by
    simpa only [W, f₁, f₂, f₃, f₄, hAc, hBc] using mixed_square_term A B x s θ
  have hAbs (s : ℂ) (hs : 1 < s.re) :
      Summable (fun x => ‖f₁ x s‖) ∧ Summable (fun x => ‖f₂ x s‖) ∧
        Summable (fun x => ‖f₃ x s‖) ∧ Summable (fun x => ‖f₄ x s‖) :=
    ⟨summable_norm_pairTerm hconv hT hT.conjugate P Pc hP hPc s hs,
      summable_norm_pairTerm hconv hU hU.conjugate Q Qc hQ hQc s hs,
      summable_norm_pairTerm hconv hT hU P Q hP hQ _ (by rw [re_add_shift]; exact hs),
      summable_norm_pairTerm hconv hT.conjugate hU.conjugate Pc Qc hPc hQc _
        (by rw [re_sub_shift]; exact hs)⟩
  have hsum : SummableAt (SpectralSquare.coeff W) logExponent 2 := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hAbs 2 (by norm_num)
    refine ((h₁.add h₂).add (h₃.add h₄)).of_nonneg_of_le (fun x => ?_) (fun x => ?_)
    · exact mul_nonneg (SpectralSquare.coeff_nonneg W x) (Real.exp_pos _).le
    · have hn := GeneralDirichlet.norm_term (SpectralSquare.coeff W) logExponent x (2 : ℂ)
      rw [abs_of_nonneg (SpectralSquare.coeff_nonneg W x), show (2 : ℂ).re = 2 by norm_num] at hn
      rw [← hn, hterm]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
  let L₃ (s : ℂ) := D₃.L (s + θ * Complex.I)
  let L₄ (s : ℂ) := D₄.L (s - θ * Complex.I)
  have h₃mero : MeromorphicOn L₃ {s : ℂ | 0 < s.re} :=
    fun _ _ => meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mpr (D₃.euler.1 _ (Set.mem_univ _))
  have h₄mero : MeromorphicOn L₄ {s : ℂ | 0 < s.re} :=
    fun _ _ => meromorphicAt_fun_comp_sub_const_iff_meromorphicAt.mpr (D₄.euler.1 _ (Set.mem_univ _))
  have h₃ord : 0 ≤ meromorphicOrderAt L₃ 1 := by
    unfold L₃
    rwa [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  have hOther (σ : ℝ) (hσ : 0 < σ) (h1 : σ ≠ 1) :
      0 ≤ meromorphicOrderAt D₁.L (σ : ℂ) ∧ 0 ≤ meromorphicOrderAt D₂.L (σ : ℂ) ∧
        0 ≤ meromorphicOrderAt L₃ (σ : ℂ) ∧ 0 ≤ meromorphicOrderAt L₄ (σ : ℂ) := by
    have hc : ((θ : ℂ) * Complex.I).re = 0 := by simp
    refine ⟨?_, ?_, order_nonneg_real_add D₃.analytic hc σ hσ h1, ?_⟩
    · simpa using order_nonneg_real_add D₁.analytic Complex.zero_re σ hσ h1
    · simpa using order_nonneg_real_add D₂.analytic Complex.zero_re σ hσ h1
    · exact order_nonneg_real_add D₄.analytic (c := -((θ : ℂ) * Complex.I))
        (by rw [Complex.neg_re, hc, neg_zero]) σ hσ h1
  have hNorm (σ : ℝ) (hσ : 1 < σ) : ‖L₃ (σ : ℂ)‖ = ‖L₄ (σ : ℂ)‖ := by
    have hconj_arg : conj ((σ : ℂ) + θ * Complex.I) = (σ : ℂ) - θ * Complex.I := by
      rw [map_add, Complex.conj_ofReal, conj_imaginaryShift, sub_eq_add_neg]
    have heq : L₄ (σ : ℂ) = conj (L₃ (σ : ℂ)) := by
      dsimp only [L₃, L₄]
      rw [D₃.exp_eq_pairTerm _ (by simpa only [re_add_shift, Complex.ofReal_re] using hσ),
        D₄.exp_eq_pairTerm _ (by simpa only [re_sub_shift, Complex.ofReal_re] using hσ),
        ← Complex.exp_conj, Complex.conj_tsum]
      congr 1
      apply tsum_congr
      intro x
      rw [← hconj_arg]
      exact (by simpa only [hAc, hBc] using pairTerm_conjugate A B x ((σ : ℂ) + θ * Complex.I))
    rw [heq, Complex.norm_conj]
  have hEq (s : ℂ) (hs : 2 < s.re) :
      D₁.L s * D₂.L s * (L₃ s * L₄ s) = Complex.exp (series (SpectralSquare.coeff W) logExponent s) := by
    have hs' : 1 < s.re := one_lt_two.trans hs
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hAbs s hs'
    dsimp only [L₃, L₄]
    rw [D₁.exp_eq_pairTerm s hs', D₂.exp_eq_pairTerm s hs',
      D₃.exp_eq_pairTerm _ (by rwa [re_add_shift]), D₄.exp_eq_pairTerm _ (by rwa [re_sub_shift])]
    change Complex.exp (∑' x, f₁ x s) * Complex.exp (∑' x, f₂ x s) *
      (Complex.exp (∑' x, f₃ x s) * Complex.exp (∑' x, f₄ x s)) = _
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
      ← h₁.of_norm.tsum_add h₂.of_norm, ← h₃.of_norm.tsum_add h₄.of_norm,
      ← (h₁.of_norm.add h₂.of_norm).tsum_add (h₃.of_norm.add h₄.of_norm)]
    exact congrArg Complex.exp (tsum_congr fun x => (hterm x s).symm)
  have h := SpectralSquare.crossOrder_eq_zero (Nat.add_pos_left (Nat.succ_pos r) (t + 1)) W
    (combinedSpectrum_has_large_eigenvalue B θ (spectra_has_large_eigenvalue hT P Pc hP hPc hTc))
    hsum (fun z _ => D₁.euler.1 z (Set.mem_univ z)) (fun z _ => D₂.euler.1 z (Set.mem_univ z))
    h₃mero h₄mero D₁.order_ge_neg_one D₂.order_ge_neg_one h₃ord hOther hNorm hEq
  dsimp only [L₃] at h
  rwa [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt] at h

private theorem order_eq_of_rightHalfPlane {L M : ℂ → ℂ}
    (hL : MeromorphicOn L Set.univ) (hM : MeromorphicOn M Set.univ) {σ : ℝ}
    (hEq : ∀ s : ℂ, σ < s.re → L s = M s) (z : ℂ) :
    meromorphicOrderAt L z = meromorphicOrderAt M z := by
  have hdiff : MeromorphicOn (fun s => L s - M s) Set.univ := hL.sub hM
  let a : ℂ := ((σ + 1 : ℝ) : ℂ)
  have ha : a ∈ {s : ℂ | σ < s.re} := by
    change σ < a.re
    simp [a]
  have hnear : ∀ᶠ s in 𝓝[≠] a, σ < s.re :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ha)
  have ho : meromorphicOrderAt (fun s => L s - M s) a = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (hnear.mono fun s hs => sub_eq_zero.mpr (hEq s hs))
  have hz := hdiff.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ a) (Set.mem_univ z) ho
  exact meromorphicOrderAt_congr ((meromorphicOrderAt_eq_top_iff.mp hz).mono fun _ hs =>
    sub_eq_zero.mp hs)

private theorem order_le_of_superset {S S' : Finset (FinitePlace F)}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {Q : CuspidalSpectralPresentation.{u, uQ} U}
    {hP : P.exceptional ⊆ S} {hQ : Q.exceptional ⊆ S}
    {hP' : P.exceptional ⊆ S'} {hQ' : Q.exceptional ⊆ S'}
    (hSS' : S ⊆ S') (D : ContinuedPair P Q hP hQ) (D' : ContinuedPair P Q hP' hQ') (z : ℂ) :
    meromorphicOrderAt D.L z ≤ meromorphicOrderAt D'.L z := by
  classical
  let W : Set (PlaceOutside S) := {v | (v : FinitePlace F) ∈ S'}
  have hW : W.Finite := S'.finite_toSet.preimage Subtype.val_injective.injOn
  let _ := hW.fintype
  let g (v : PlaceOutside S) (s : ℂ) :=
    (pairEulerPolynomial (spectra P hP v) (spectra Q hQ v)).eval
      (RankinSelberg.spectralPoint (residueCardinality v.1) s)
  let H (s : ℂ) := ∏ w : ↥W, g w.1 s
  have hg (v : PlaceOutside S) : Differentiable ℂ (g v) := by
    have hq : (residueCardinality v.1 : ℂ) ≠ 0 := by
      have := CuspidalPairEulerConvergence.two_le_residueCardinality v.1
      exact_mod_cast (show residueCardinality v.1 ≠ 0 by omega)
    have hp : Differentiable ℂ (RankinSelberg.spectralPoint (residueCardinality v.1)) := by
      intro s
      unfold RankinSelberg.spectralPoint
      exact (differentiableAt_id.neg).const_cpow (Or.inl hq)
    exact (Polynomial.differentiable (pairEulerPolynomial (spectra P hP v) (spectra Q hQ v))).comp hp
  have hH : Differentiable ℂ H := Differentiable.fun_finsetProd (fun v _ => hg v.1)
  have hM : MeromorphicOn (fun s => H s * D.L s) Set.univ := fun s hs =>
    (hH.analyticAt s).meromorphicAt.mul (D.euler.1 s hs)
  obtain ⟨σ, hσ⟩ := D.euler.2
  obtain ⟨σ', hσ'⟩ := D'.euler.2
  let e : ↥(Wᶜ) ≃ PlaceOutside S' :=
    { toFun := fun v => ⟨v.1.1, v.2⟩
      invFun := fun v => ⟨⟨v.1, fun hv => v.2 (hSS' hv)⟩, v.2⟩
      left_inv := fun v => Subtype.ext (Subtype.ext rfl)
      right_inv := fun v => Subtype.ext rfl }
  have hEq (s : ℂ) (hs : max (max σ σ') 1 < s.re) : H s * D.L s = D'.L s := by
    have hsmall : σ < s.re := ((le_max_left _ _).trans (le_max_left _ _)).trans_lt hs
    have hlarge : σ' < s.re := ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hs
    have hone : 1 < s.re := (le_max_right _ _).trans_lt hs
    let f (v : PlaceOutside S) := (g v s)⁻¹
    have hprod : HasProd f (D.L s) := (hσ s hsmall).2
    have hprod' : HasProd (fun w : ↥(Wᶜ) => f w.1) (D'.L s) :=
      (e.hasProd_iff.mpr (hσ' s hlarge).2).congr_fun (fun _ => rfl)
    have hmul : D.L s = (∏ w : ↥W, f w.1) * D'.L s :=
      hprod.unique ((hasProd_fintype (fun w : ↥W => f w.1)).mul_compl hprod')
    have hn (w : ↥W) : g w.1 s ≠ 0 := by
      intro hz
      have hf : f w.1 = 0 := by simp [f, hz]
      have hz' := Finset.prod_eq_zero (f := fun w : ↥W => f w.1) (Finset.mem_univ w) hf
      have hnonzero : D.L s ≠ 0 := by
        rw [D.exp_eq s hone]
        exact Complex.exp_ne_zero _
      apply hnonzero
      rw [hmul, hz', zero_mul]
    have hcancel : H s * (∏ w : ↥W, f w.1) = 1 := by
      dsimp only [H]
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (hn w)
    rw [hmul, ← mul_assoc, hcancel, one_mul]
  have hMOrd := order_eq_of_rightHalfPlane hM D'.euler.1 hEq z
  rw [← hMOrd]
  change meromorphicOrderAt D.L z ≤ meromorphicOrderAt (H * D.L) z
  rw [meromorphicOrderAt_mul (hH.analyticAt z).meromorphicAt (D.euler.1 z (Set.mem_univ z))]
  exact le_add_of_nonneg_left (hH.analyticAt z).meromorphicOrderAt_nonneg

private theorem order_cross_any (hconv : CuspidalPairAbsoluteConvergenceStatement.{u, uQ})
    (hcont : PartialPairContinuationAt.{u, uQ} F)
    (hT : HasUnitaryCentralCharacter T) (hU : HasUnitaryCentralCharacter U)
    (hTs : IsTrivialOnSplitCentre T) (hUs : IsTrivialOnSplitCentre U)
    {S : Finset (FinitePlace F)}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {Q : CuspidalSpectralPresentation.{u, uQ} U}
    (hPa : HasIrreducibleAdmissibleComponents P) (hQa : HasIrreducibleAdmissibleComponents Q)
    {hP : P.exceptional ⊆ S} {hQ : Q.exceptional ⊆ S}
    (D : ContinuedPair P Q hP hQ) (θ : ℝ)
    (h : ¬ (θ = 0 ∧ ∃ hrt : r = t,
      OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) U.realization)) :
    meromorphicOrderAt D.L (1 + θ * Complex.I) = 0 := by
  classical
  have hTc := RankinSelbergGlobal.SelfPair.conjugate_isContragredientOf T hT
  have hUc := RankinSelbergGlobal.SelfPair.conjugate_isContragredientOf U hU
  obtain ⟨Pc, hPca⟩ := Automorphic.cuspidalContragredientPresentationExistence.{u, uQ, uQ}
    F r T T.conjugate hT hTc P
  obtain ⟨Qc, hQca⟩ := Automorphic.cuspidalContragredientPresentationExistence.{u, uQ, uQ}
    F t U U.conjugate hU hUc Q
  let S' := S ∪ Pc.exceptional ∪ Qc.exceptional
  have hSS' : S ⊆ S' := Finset.subset_union_left.trans Finset.subset_union_left
  have hPc : Pc.exceptional ⊆ S' := Finset.subset_union_right.trans Finset.subset_union_left
  have hQc : Qc.exceptional ⊆ S' := Finset.subset_union_right
  have hPt := hP.trans hSS'
  have hQt := hQ.trans hSS'
  have hTcs := NormPowerTwist.isTrivialOnSplitCentre_conjugate hTs
  have hUcs := NormPowerTwist.isTrivialOnSplitCentre_conjugate hUs
  obtain ⟨D₁⟩ := continuedPair_exists hcont hT hT.conjugate hTs hTcs P Pc hPa hPca hPt hPc
  obtain ⟨D₂⟩ := continuedPair_exists hcont hU hU.conjugate hUs hUcs Q Qc hQa hQca hQt hQc
  obtain ⟨D₃⟩ := continuedPair_exists hcont hT hU hTs hUs P Q hPa hQa hPt hQt
  obtain ⟨D₄⟩ := continuedPair_exists hcont hT.conjugate hU.conjugate hTcs hUcs Pc Qc
    hPca hQca hPc hQc
  have hlarge := order_cross hconv hT hU hTc hUc D₁ D₂ D₃ D₄ θ (order_nonneg_boundary D₃ θ h)
  exact (order_le_of_superset hSS' D D₃ _ |>.trans hlarge.le).antisymm (order_nonneg_boundary D θ h)

end Presentations

/-- The partial continuation with its pole bounds implies the normalized
logarithm limits for cuspidal pairs. -/
def LandauAsymptoticsReductionStatement : Prop :=
  CuspidalPairAbsoluteConvergenceStatement.{u, uQ} →
    ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
      PartialPairContinuationAt.{u, uQ} F → CuspidalPairLogAsymptoticsAt.{u, uQ} F

theorem landauAsymptoticsReduction : LandauAsymptoticsReductionStatement.{u, uQ} := by
  intro hconv F _ _ _ hcont r t T U hT hU hTs hUs P Q hPa hQa S hP hQ θ
  obtain ⟨D⟩ := continuedPair_exists hcont hT hU hTs hUs P Q hPa hQa hP hQ
  let l (σ : ℝ) := ∑' x : LogIndex S, logEulerTerm P Q hP hQ x.1 x.2 ((σ : ℂ) + θ * Complex.I)
  have hD := CuspidalPairPartialContinuation.differentiableOn_logSeries P Q hP hQ
    (fun σ hσ => (hconv F r t T U hT hU P Q S hP hQ (σ : ℂ) (by simpa using hσ)).1)
  have hLc : ContinuousOn l (Set.Ioo 1 (2 : ℝ)) :=
    hD.continuousOn.comp (by fun_prop) (fun σ hσ => by
      change 1 < ((σ : ℂ) + θ * Complex.I).re
      rw [re_add_shift, Complex.ofReal_re]
      exact hσ.1)
  have hLog {n : ℤ} (ho : meromorphicOrderAt D.L (1 + θ * Complex.I) = n) :
      Tendsto (fun σ : ℝ => l σ / (Real.log (1 / (σ - 1)) : ℂ)) (𝓝[>] 1) (𝓝 (-n : ℂ)) :=
    LogarithmicAsymptotics.tendsto_div_log_of_meromorphicOrderAt
      (D.euler.1 _ (Set.mem_univ _)) ho (by norm_num) hLc
      (fun σ hσ => (D.exp_eq _ (by simpa only [re_add_shift, Complex.ofReal_re] using hσ.1)).symm)
  constructor
  · rintro ⟨hθ, ⟨hrt, hd⟩⟩
    have ho : meromorphicOrderAt D.L (1 + θ * Complex.I) = (-1 : ℤ) := by
      subst θ
      subst t
      simpa using order_self hconv hU hT hd D
    simpa [l] using hLog ho
  · intro h
    have ho : meromorphicOrderAt D.L (1 + θ * Complex.I) = (0 : ℤ) :=
      order_cross_any hconv hcont hT hU hTs hUs hPa hQa D θ h
    simpa [l] using hLog ho

end Langlands.Global.CuspidalPairLandauOrders
