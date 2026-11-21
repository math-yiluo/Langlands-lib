import Langlands.Global.Factors.CuspidalPairPoleFieldwise
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof
import Langlands.Global.Factors.CuspidalFinitePairRegularityStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Automorphic.CuspidalArchimedeanComponentStatement
import Langlands.Representation.Conductor.SphericalLaurentFunctionalEquationReduction

/-! # Partial cuspidal pair L-functions from completed pole data

Multiplying the completed L-function by the omitted denominators gives
a meromorphic representative of the partial product. Its pole order can only
improve. The two local regularity premises suffice to preserve the self-pole. -/

noncomputable section

set_option autoImplicit false

universe u uQ

open Filter Topology

namespace Langlands.Global

open NumberField Polynomial
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents pairEulerPolynomial
  residueCardinality)
open CuspidalPairBoundaryNonvanishing (partialEulerFactor IsPartialPairLFunction)
open CuspidalPairAbsoluteConvergence CuspidalPairPoles
open LocalFactor.Archimedean
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPairPartialContinuation

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- At a place outside both exceptional sets, the pair L-polynomial of a finite choice for the
pole statement is the unramified pair Euler polynomial of the two spectra. -/
private theorem lPolynomial_eq_pairEulerPolynomial {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} {P : CuspidalSpectralPresentation.{u, uQ} T}
    {P' : CuspidalSpectralPresentation.{u, uQ} T'} {h : HasIrreducibleAdmissibleComponents P}
    {h' : HasIrreducibleAdmissibleComponents P'} (c : CuspidalPairPoles.FinitePairLChoice P P' h h')
    (v : FinitePlace F) (hv : v ∉ P.exceptional) (hv' : v ∉ P'.exceptional) :
    c.lPolynomial v = pairEulerPolynomial (P.spectralSystem.eigenvalues v hv)
      (P'.spectralSystem.eigenvalues v hv') :=
  CuspidalPairFunctionalEquation.isAutomorphicPairLPolynomial_eq_pairEulerPolynomial
    (CompletionPadic.padicField v) (c.additive v) (c.measure_spec v) _ _
    (CuspidalPairFunctionalEquation.hasSphericalSpectrum_padicObject P h v hv)
    (CuspidalPairFunctionalEquation.hasSphericalSpectrum_padicObject P' h' v hv')
    (c.lPolynomial_spec v)

/-- A finite product of reciprocal-entire denominators has isolated zeros. -/
private theorem prod_denominator_eventually_ne_zero {ι : Type*} (s : Finset ι)
    (f : ι → LocalFactor.ReciprocalEntire) (z : ℂ) :
    ∀ᶠ w in nhdsWithin z {z}ᶜ, ∏ i ∈ s, (f i).denominator w ≠ 0 := by
  have h : ∀ i ∈ s, ∀ᶠ w in nhdsWithin z {z}ᶜ, (f i).denominator w ≠ 0 :=
    fun i _ => (f i).denominator_eventually_ne_zero z
  filter_upwards [(Filter.eventually_all_finset s).mpr h] with w hw
  exact Finset.prod_ne_zero_iff.mpr hw

private theorem differentiable_prod_denominator {ι : Type*} (s : Finset ι)
    (f : ι → LocalFactor.ReciprocalEntire) :
    Differentiable ℂ (fun w => ∏ i ∈ s, (f i).denominator w) := by
  exact Differentiable.fun_finsetProd (fun i _ => (f i).entire)

/-- `s ↦ q ^ (-s)` is entire for `q ≥ 1`. -/
private theorem differentiable_spectralPoint {q : ℕ} (hq : 0 < q) :
    Differentiable ℂ (RankinSelberg.spectralPoint q) := by
  intro s
  unfold RankinSelberg.spectralPoint
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  exact (differentiableAt_id.neg).const_cpow (Or.inl hq0)

private theorem differentiable_eval_spectralPoint (p : ℂ[X]) {q : ℕ} (hq : 0 < q) :
    Differentiable ℂ (fun s => p.eval (RankinSelberg.spectralPoint q s)) :=
  (Polynomial.differentiable p).comp (differentiable_spectralPoint hq)

/-- The terms of the double series decrease with the real part. -/
private theorem norm_logEulerTerm_le_of_le_re {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (x : {v : FinitePlace F // v ∉ S} × ℕ) {s : ℂ} {σ : ℝ} (hσ : σ ≤ s.re) :
    ‖logEulerTerm P P' hP hP' x.1 x.2 s‖ ≤ ‖logEulerTerm P P' hP hP' x.1 x.2 (σ : ℂ)‖ := by
  rw [norm_logEulerTerm, norm_logEulerTerm, Complex.ofReal_re]
  have hl : 0 ≤ logExponent x := (Real.log_pos one_lt_two).le.trans (log_two_le_logExponent x)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Each term of the double series is entire in `s`. -/
private theorem differentiable_logEulerTerm {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (x : {v : FinitePlace F // v ∉ S} × ℕ) :
    Differentiable ℂ (fun s => logEulerTerm P P' hP hP' x.1 x.2 s) := by
  have hq : 0 < residueCardinality x.1.1 := by
    have := CuspidalPairEulerConvergence.two_le_residueCardinality x.1.1
    omega
  unfold logEulerTerm
  exact ((differentiable_const _).mul
    ((differentiable_spectralPoint hq).pow _)).div_const _

/-- **Holomorphy of the double series on `Re s > 1`**, from its absolute convergence at real
points `σ > 1`. -/
theorem differentiableOn_logSeries {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hsum : ∀ σ : ℝ, 1 < σ →
      Summable fun x : {v : FinitePlace F // v ∉ S} × ℕ => ‖logEulerTerm P P' hP hP' x.1 x.2 σ‖) :
    DifferentiableOn ℂ (fun s => ∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
      logEulerTerm P P' hP hP' x.1 x.2 s) {s : ℂ | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : (1 : ℝ) < s₀.re := hs₀
  set σ₀ : ℝ := (1 + s₀.re) / 2 with hσ₀
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; linarith
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : s₀ ∈ {s : ℂ | σ₀ < s.re} := by
    show σ₀ < s₀.re
    rw [hσ₀]; linarith
  have hd := Complex.differentiableOn_tsum_of_summable_norm (hsum σ₀ hσ₀1)
    (fun x => (differentiable_logEulerTerm P P' hP hP' x).differentiableOn) hU
    (fun x w hw => norm_logEulerTerm_le_of_le_re P P' hP hP' x (le_of_lt hw))
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

/-- `-1 ≤ n < 0` forces `n = -1` in `WithTop ℤ`. -/
private theorem eq_neg_one_of_le_of_lt {n : WithTop ℤ} (h1 : -1 ≤ n) (h2 : n < 0) : n = -1 := by
  induction n with
  | top => exact absurd h2 (not_lt.mpr le_top)
  | coe m =>
    have h1' : (-1 : ℤ) ≤ m := WithTop.coe_le_coe.mp (h1 : ((-1 : ℤ) : WithTop ℤ) ≤ m)
    have h2' : m < 0 := WithTop.coe_lt_coe.mp (h2 : (m : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ))
    have : m = -1 := by omega
    rw [this]
    rfl

/-- Partial pair continuation and pole bounds over `F`, with pole preservation
when the local denominators at `1` are nonzero by the regularity statements. -/
def PartialPairContinuationAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T'),
      HasIrreducibleAdmissibleComponents P → HasIrreducibleAdmissibleComponents P' →
    ∀ (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S),
    ∃ L : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        L s = Complex.exp (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
          logEulerTerm P P' hP hP' x.1 x.2 s)) ∧
      IsPartialPairLFunction P P' hP hP' L ∧
      (∀ z : ℂ, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ L z) ∧
      (-1 ≤ meromorphicOrderAt L 1) ∧
      ((¬ ∃ hrt : r = t, OperatorRealization.IsContragredientOf (n := t + 1)
          (hrt ▸ T.realization) T'.realization) → 0 ≤ meromorphicOrderAt L 1) ∧
      (Automorphic.CuspidalArchimedeanPairRegularityStatement.{u} →
        CuspidalFinitePairRegularityStatement.{u, uQ} →
        (∃ hrt : r = t, OperatorRealization.IsContragredientOf (n := t + 1)
          (hrt ▸ T.realization) T'.realization) → meromorphicOrderAt L 1 = -1)

/-- A certified completed L-function with its simple pole profile for each pair
of split-centre-trivial cuspidal presentations. The witnesses include the finite
L-data and the parameters at the real and complex places. -/
def CompletedPoleProfileAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
      (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P'),
    ∃ (c : FinitePairLChoice P P' h h')
      (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
      (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
      (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) ∧
      (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) ∧
      (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) ∧
      (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) ∧
      ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ ∧
        HasSimplePoleProfile Λ (∃ hrt : r = t,
          OperatorRealization.IsContragredientOf (n := t + 1)
            (hrt ▸ T.realization) T'.realization)

/-- Choose one completed L-function with its pole profile from the fieldwise pole theorem. -/
theorem completedPoleProfileAt_of_poleAt (hPole : CuspidalPairPoleAt.{u, uQ} F) :
    CompletedPoleProfileAt.{u, uQ} F := by
  classical
  intro r t T T' htriv htriv' P P' h h'
  obtain ⟨⟨⟨c⟩, hR, hC⟩, hmain⟩ := hPole r t T T' htriv htriv' P P' h h'
  choose dR hdR using fun v => (hR v).1
  choose dR' hdR' using fun v => (hR v).2
  choose dC hdC using fun v => (hC v).1
  choose dC' hdC' using fun v => (hC v).2
  obtain ⟨Λ, hCompleted, hProfile, _⟩ := hmain c dR dR' hdR hdR' dC dC' hdC hdC'
  exact ⟨c, dR, dR', dC, dC', hdR, hdR', hdC, hdC', Λ, hCompleted, hProfile⟩

set_option maxHeartbeats 4000000 in
/-- **The partial pair L-function near `Re s = 1`.** Under the completed pole profile and the absolute
convergence for `Re s > 1`, there is a function `L`, meromorphic on `ℂ`, equal to
`exp (l(s))` on `Re s > 1`, with no pole outside `{0, 1}` and order at least `-1` at `1`.
The order at `1` is nonnegative unless `T` realizes the contragredient of `T'`,
and the local regularity statements give a simple pole in the contragredient case. -/
theorem exists_partialPairL_of_completedPoleProfile (hPole : CompletedPoleProfileAt.{u, uQ} F)
    (hconv : CuspidalPairAbsoluteConvergenceStatement.{u, uQ}) :
    PartialPairContinuationAt.{u, uQ} F := by
  classical
  intro r t T T' hT hT' htriv htriv' P P' h h' S hP hP'
  obtain ⟨c, dR, dR', dC, dC', hdR, hdR', hdC, hdC', Λ, ⟨σΛ, hσΛ⟩, ⟨hΛd, hΛp⟩⟩ :=
    hPole r t T T' htriv htriv' P P' h h'
  -- the auxiliary functions
  let Dinf : ℂ → ℂ := fun s => (∏ v, (realPairLFactor (dR v) (dR' v)).denominator s) *
    ∏ v, (complexPairLFactor (dC v) (dC' v)).denominator s
  let polyS : ℂ → ℂ := fun s => ∏ v ∈ S,
    (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s)
  let G : ℂ → ℂ := fun s => Dinf s * polyS s
  let L : ℂ → ℂ := fun s => G s * Λ s
  let ser : ℂ → ℂ := fun s => ∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
    logEulerTerm P P' hP hP' x.1 x.2 s
  have hq : ∀ v : FinitePlace F, 0 < residueCardinality v := fun v => by
    have := CuspidalPairEulerConvergence.two_le_residueCardinality v
    omega
  have hGd : Differentiable ℂ G :=
    ((differentiable_prod_denominator _ _).mul
      (differentiable_prod_denominator _ _)).mul
      (Differentiable.fun_finsetProd fun v _ =>
        differentiable_eval_spectralPoint _ (hq v))
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ := (Set.toFinite _).isClosed.isOpen_compl
  have hΛan : ∀ z : ℂ, z ∉ ({0, 1} : Set ℂ) → AnalyticAt ℂ Λ z := fun z hz =>
    hΛd.analyticAt (hopen.mem_nhds hz)
  have hΛmero : ∀ z : ℂ, MeromorphicAt Λ z := by
    intro z
    by_cases hz : z ∈ ({0, 1} : Set ℂ)
    · exact (hΛp z hz).1
    · exact (hΛan z hz).meromorphicAt
  have hre1 : ∀ z : ℂ, 1 < z.re → z ∉ ({0, 1} : Set ℂ) := by
    intro z hz hmem
    rcases hmem with h0 | h1
    · rw [h0, Complex.zero_re] at hz; linarith
    · rw [Set.mem_singleton_iff] at h1
      rw [h1, Complex.one_re] at hz; linarith
  -- holomorphy on `Re s > 1`
  have hLd : DifferentiableOn ℂ L {s : ℂ | 1 < s.re} := by
    intro s hs
    exact ((hGd s).mul ((hΛan s (hre1 s hs)).differentiableAt)).differentiableWithinAt
  have hserd : DifferentiableOn ℂ ser {s : ℂ | 1 < s.re} :=
    differentiableOn_logSeries P P' hP hP' (fun σ hσ =>
      (hconv F r t T T' hT hT' P P' S hP hP' (σ : ℂ) (by rwa [Complex.ofReal_re])).1)
  -- thresholds for the L-polynomials at the places of `S`
  have hpoly : ∀ v : FinitePlace F, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s) ≠ 0 := by
    intro v
    apply Conductor.exists_halfPlane_eval_spectralPoint_ne_zero
      (CuspidalPairEulerConvergence.two_le_residueCardinality v) _
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Correspondence.IsAutomorphicPairLPolynomial.coeff_zero (c.lPolynomial_spec v)]
    exact one_ne_zero
  choose σp hσp using hpoly
  set σ₁ : ℝ := max (max σΛ 2) (∑ v ∈ S, |σp v|) with hσ₁
  have hσp_le : ∀ v ∈ S, σp v ≤ σ₁ := by
    intro v hv
    calc σp v ≤ |σp v| := le_abs_self _
      _ ≤ ∑ w ∈ S, |σp w| := Finset.single_le_sum (fun w _ => abs_nonneg (σp w)) hv
      _ ≤ σ₁ := le_max_right _ _
  have hσΛ₁ : σΛ ≤ σ₁ := (le_max_left σΛ 2).trans (le_max_left _ _)
  have h2₁ : (2 : ℝ) ≤ σ₁ := (le_max_right σΛ 2).trans (le_max_left _ _)
  -- the identity on a far half-plane, off the zeros of the archimedean denominators
  have heq : ∀ s : ℂ, σ₁ < s.re → Dinf s ≠ 0 → L s = Complex.exp (ser s) := by
    intro s hs' hDs
    obtain ⟨hsumΛ, p, hp, hΛs⟩ := hσΛ s (by linarith)
    unfold archimedeanPairProduct at hΛs
    obtain ⟨-, -, hprod⟩ := hconv F r t T T' hT hT' P P' S hP hP' s (by linarith)
    have hinf : ((∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹) * Dinf s = 1 := by
      have hD1 := left_ne_zero_of_mul hDs
      have hD2 := right_ne_zero_of_mul hDs
      rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
      change _ * ((∏ v, (realPairLFactor (dR v) (dR' v)).denominator s) *
        ∏ v, (complexPairLFactor (dC v) (dC' v)).denominator s) = 1
      field_simp
    let f : FinitePlace F → ℂ := fun v => c.finiteL v s
    have hfS : ∀ v (hv : v ∉ S), f v = partialEulerFactor P P' hP hP' ⟨v, hv⟩ s := by
      intro v hv
      simp only [f, FinitePairLChoice.finiteL, partialEulerFactor]
      rw [lPolynomial_eq_pairEulerPolynomial c v (fun h => hv (hP h))
        (fun h => hv (hP' h))]
    have hsumc : Summable fun v : ↥((↑S : Set (FinitePlace F))ᶜ) => ‖f v - 1‖ :=
      hsumΛ.comp_injective Subtype.val_injective
    have hfc := CuspidalPairEulerConvergence.hasProd_of_summable_norm_sub_one hsumc
    set b := ∏' v : ↥((↑S : Set (FinitePlace F))ᶜ), f v
    have hpf : p = (∏ v ∈ S, f v) * b := hp.unique ((S.hasProd f).mul_compl hfc)
    have hserb : Complex.exp (ser s) = b := by
      let e : ↥((↑S : Set (FinitePlace F))ᶜ) ≃ {v : FinitePlace F // v ∉ S} :=
        Equiv.subtypeEquivRight (fun v => Iff.rfl)
      have h1 := e.hasProd_iff.mpr hprod
      have h2 : HasProd (fun v : ↥((↑S : Set (FinitePlace F))ᶜ) => f v)
          (Complex.exp (ser s)) :=
        h1.congr_fun (fun v => hfS v.1 v.2)
      exact h2.unique hfc
    have hfpoly : (∏ v ∈ S, f v) * polyS s = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro v hv
      have hne := hσp v s ((hσp_le v hv).trans_lt hs')
      simp only [f, FinitePairLChoice.finiteL]
      exact inv_mul_cancel₀ hne
    calc L s = (((∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
          ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹) * Dinf s) *
          ((∏ v ∈ S, f v) * polyS s) * b := by
          simp only [L, G]
          rw [hΛs, hpf]
          ring
      _ = Complex.exp (ser s) := by
          rw [hinf, hfpoly, hserb]
          ring
  -- the identity theorem on `Re s > 1`
  have hUopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hDiso : ∀ z, ∀ᶠ w in 𝓝[≠] z, Dinf w ≠ 0 := fun z =>
    ((prod_denominator_eventually_ne_zero _ _ z).and
      (prod_denominator_eventually_ne_zero _ _ z)).mono
        fun w hw => mul_ne_zero hw.1 hw.2
  set z₀ : ℂ := ((σ₁ + 1 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = σ₁ + 1 := by rw [hz₀, Complex.ofReal_re]
  have hz₀U : z₀ ∈ {s : ℂ | 1 < s.re} := by
    show 1 < z₀.re
    rw [hz₀re]; linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] z₀, L w = Complex.exp (ser w) := by
    have hnear : ∀ᶠ w in 𝓝[≠] z₀, σ₁ < w.re :=
      eventually_nhdsWithin_of_eventually_nhds
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show σ₁ < z₀.re by rw [hz₀re]; linarith))
    exact (((hDiso z₀).and hnear).mono fun w hw => heq w hw.2 hw.1).frequently
  have hEq : Set.EqOn L (fun s => Complex.exp (ser s)) {s : ℂ | 1 < s.re} :=
    (hLd.analyticOnNhd hUopen).eqOn_of_preconnected_of_frequently_eq
      (hserd.cexp.analyticOnNhd hUopen) hUc hz₀U hfreq
  have hLeq : ∀ s : ℂ, 1 < s.re → L s = Complex.exp (ser s) := fun s hs => hEq hs
  -- meromorphy and orders
  have hGan : ∀ z, AnalyticAt ℂ G z := fun z => hGd.analyticAt z
  have hLmero : ∀ z, MeromorphicAt L z := fun z => (hGan z).meromorphicAt.mul (hΛmero z)
  have hordL : ∀ z, meromorphicOrderAt L z =
      meromorphicOrderAt G z + meromorphicOrderAt Λ z := fun z =>
    meromorphicOrderAt_mul (hGan z).meromorphicAt (hΛmero z)
  have hmem1 : (1 : ℂ) ∈ ({0, 1} : Set ℂ) := by simp
  refine ⟨L, hLeq, ⟨fun z _ => hLmero z, 1, fun s hs => ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, h2, h3⟩ := hconv F r t T T' hT hT' P P' S hP hP' s hs
    refine ⟨h2, ?_⟩
    rw [hLeq s hs]
    exact h3
  · intro z hz0 hz1
    exact (hGan z).mul (hΛan z (by simp [hz0, hz1]))
  · rw [hordL 1]
    exact (hΛp 1 hmem1).2.1.trans
      (le_add_of_nonneg_left (hGan 1).meromorphicOrderAt_nonneg)
  · intro hnc
    rw [hordL 1]
    refine add_nonneg (hGan 1).meromorphicOrderAt_nonneg ?_
    exact not_lt.mp fun hlt => hnc ((hΛp 1 hmem1).2.2.mp hlt)
  · intro hArch hFin hcond
    obtain ⟨hAR, hAC⟩ := hArch F r t T T' hT hT'
    have hre : (1 : ℝ) ≤ (1 : ℂ).re := by rw [Complex.one_re]
    have hG1 : G 1 ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact Finset.prod_ne_zero_iff.mpr fun v _ =>
          hAR v (dR v) (dR' v) (hdR v) (hdR' v) 1 hre
      · exact Finset.prod_ne_zero_iff.mpr fun v _ =>
          hAC v (dC v) (dC' v) (hdC v) (hdC' v) 1 hre
      · exact Finset.prod_ne_zero_iff.mpr fun v _ =>
          hFin F r t T T' hT hT' P P' h h' c v 1 hre
    have h1 : meromorphicOrderAt L 1 = meromorphicOrderAt Λ 1 :=
      meromorphicOrderAt_mul_of_ne_zero (hGan 1) hG1
    rw [h1]
    exact eq_neg_one_of_le_of_lt (hΛp 1 hmem1).2.1 ((hΛp 1 hmem1).2.2.mpr hcond)

/-- The fieldwise pole theorem supplies the completed data for the partial L-function. -/
theorem exists_partialPairL (hPole : CuspidalPairPoleAt.{u, uQ} F)
    (hconv : CuspidalPairAbsoluteConvergenceStatement.{u, uQ}) :
    PartialPairContinuationAt.{u, uQ} F :=
  exists_partialPairL_of_completedPoleProfile (completedPoleProfileAt_of_poleAt hPole) hconv

/-- The completed pair pole statement implies partial continuation over every
number field. Its totally complex form suffices for a totally complex field. -/
def PartialPairContinuationReductionStatement : Prop :=
  CuspidalPairAbsoluteConvergenceStatement.{u, uQ} →
    ((CuspidalPairPoleStatement.{u, uQ} →
      ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
        PartialPairContinuationAt.{u, uQ} F) ∧
    (CuspidalPairPoleTCStatement.{u, uQ} →
      ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
          [CompactSpace (AdeleQuotient F)], PartialPairContinuationAt.{u, uQ} F))

/-- The two reductions to the completed pair pole statement. -/
theorem partialPairContinuationReduction : PartialPairContinuationReductionStatement.{u, uQ} := by
  intro hconv
  exact ⟨fun hPole F _ _ _ => exists_partialPairL (cuspidalPairPoleAt_of_statement hPole F) hconv,
    fun hPole F _ _ _ _ => exists_partialPairL (cuspidalPairPoleAt_of_TC hPole F) hconv⟩

end CuspidalPairPartialContinuation

end Langlands.Global
