import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankUnitSpanProof
import Langlands.Representation.RankinSelberg.NormalizedGeneratorExistenceProof
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.MeasureTheory.Integral.Prod

/-!
# JPSS unequal-rank convergence, rationality and normalized generators

Transfer the published zero-row analytics through the published compact
rectangular expansion, retaining the actual coefficient models and measures.
The published unit-span and algebraic normalization theorems supply the
normalized generator for each block.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Polynomial
open scoped BigOperators

namespace UnequalRankReduction

open Langlands.HarmonicAnalysis Langlands.Whittaker

open RationalContinuationLinear

/-- Finite sums of integrable separated factors are absolutely integrable. -/
theorem integrable_separated_sum {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    (t : Finset ι) (B : ι → α → ℂ) (φ : ι → β → ℂ)
    (hB : ∀ i ∈ t, Integrable (B i) μ) (hφ : ∀ i ∈ t, Integrable (φ i) ν) :
    Integrable (fun z : α × β => ∑ i ∈ t, B i z.1 * φ i z.2) (μ.prod ν) :=
  integrable_finsetSum t (fun i hi => (hB i hi).mul_prod (hφ i hi))

/-- The prescribed order of the nested integral gives a constant linear combination. -/
theorem integral_separated_sum {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (t : Finset ι) (B : ι → α → ℂ) (φ : ι → β → ℂ)
    (hB : ∀ i ∈ t, Integrable (B i) μ) (hφ : ∀ i ∈ t, Integrable (φ i) ν) :
    (∫ q, ∫ x, ∑ i ∈ t, B i q * φ i x ∂ν ∂μ) =
      ∑ i ∈ t, (∫ x, φ i x ∂ν) * (∫ q, B i q ∂μ) := by
  calc
    (∫ q, ∫ x, ∑ i ∈ t, B i q * φ i x ∂ν ∂μ) =
        ∫ q, ∑ i ∈ t, B i q * (∫ x, φ i x ∂ν) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [integral_finsetSum t (fun i hi => (hφ i hi).const_mul (B i q))]
      simp only [integral_const_mul]
    _ = ∑ i ∈ t, (∫ x, φ i x ∂ν) * (∫ q, B i q ∂μ) := by
      rw [integral_finsetSum t (fun i hi => (hB i hi).mul_const (∫ x, φ i x ∂ν))]
      simp only [integral_mul_const, mul_comm]

/-- A finite family of right-half-plane statements has one common bound, also when empty. -/
theorem finite_common_bound {ι : Type*} [Fintype ι] (P : ι → ℂ → Prop)
    (hP : ∀ i, ∃ a : ℝ, ∀ s : ℂ, a < s.re → P i s) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re → ∀ i, P i s := by
  classical
  choose a ha using hP
  refine ⟨∑ i, |a i|, fun s hs i => ha i s ?_⟩
  have hi : a i ≤ ∑ j, |a j| := (le_abs_self (a i)).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i))
  exact hi.trans_lt hs

section ActualIntegrands

variable {F : Type*} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}

omit [TopologicalSpace F] in
/-- Setting the rectangular entries to zero leaves exactly the diagonal inclusion. -/
theorem unequalRankMatrix_at_zero (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankMatrix j k g 0 = appendIdentity n (j + k + 1) g := by
  apply Units.ext
  rw [unequalRankMatrix_val]
  have hz : rectangularEntries (n := n) (F := F) j k 0 = 0 := by
    ext a b
    simp [rectangularEntries]
  simp [hz]

/-- A finite coefficient expansion descends to the actual quotient integrands.
The diagonal terms retain the same rank gap and spectral exponent. -/
theorem integrand_of_finite_expansion (j k m : ℕ)
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
    (Ws : Fin m → WhittakerFunctions ψ (n + (j + k + 1)))
    (hexp : ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
      W.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (Ws i).val (appendIdentity n (j + k + 1) g))
    (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k W W' s x q =
      ∑ i, unequalRankIntegrand ψ abv j k (Ws i) W' s 0 q * φ i x := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk, unequalRankMatrix_at_zero, hexp,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Product-measure convergence follows from integrable diagonal and rectangular factors. -/
theorem converges_of_finite_expansion (j k m : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)) [SFinite ν]
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
    (Ws : Fin m → WhittakerFunctions ψ (n + (j + k + 1)))
    (hexp : ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
      W.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (Ws i).val (appendIdentity n (j + k + 1) g))
    (s : ℂ)
    (hWs : ∀ i, Integrable (unequalRankIntegrand ψ abv j k (Ws i) W' s 0) μ)
    (hφ : ∀ i, Integrable (φ i) ν) :
    UnequalRankConverges ψ abv j k μ ν W W' s := by
  unfold UnequalRankConverges
  simp_rw [integrand_of_finite_expansion ψ abv j k m W W' φ Ws hexp]
  exact integrable_separated_sum Finset.univ _ _ (fun i _ => hWs i) (fun i _ => hφ i)

/-- The actual nested block integral is a finite sum of diagonal integrals. -/
theorem integral_of_finite_expansion (j k m : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
    (Ws : Fin m → WhittakerFunctions ψ (n + (j + k + 1)))
    (hexp : ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
      W.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (Ws i).val (appendIdentity n (j + k + 1) g))
    (s : ℂ)
    (hWs : ∀ i, Integrable (unequalRankIntegrand ψ abv j k (Ws i) W' s 0) μ)
    (hφ : ∀ i, Integrable (φ i) ν) :
    unequalRankIntegral ψ abv j k μ ν W W' s =
      ∑ i, (∫ x, φ i x ∂ν) *
        (∫ q, unequalRankIntegrand ψ abv j k (Ws i) W' s 0 q ∂μ) := by
  unfold unequalRankIntegral
  simp_rw [integrand_of_finite_expansion ψ abv j k m W W' φ Ws hexp]
  exact integral_separated_sum Finset.univ _ _ (fun i _ => hWs i) (fun i _ => hφ i)

private theorem diagonal_value_cast {d e : ℕ} (h : d = e)
    (W : WhittakerFunctions ψ (n + e))
    (g : Langlands.GeneralLinear (n + 1) F) :
    (show WhittakerFunctions ψ (n + d) from by rw [h]; exact W).val
        (appendIdentity n d g) = W.val (appendIdentity n e g) := by
  subst e
  rfl

/-- Changing from `(j,k)` at zero to `(0,j+k)` changes only the rank spelling. -/
theorem diagonal_integrand_eq_zero_rows (j k : ℕ)
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k W W' s 0 q =
      unequalRankIntegrand ψ abv 0 (j + k)
        (by rw [Nat.zero_add]; exact W) W' s 0 q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk, unequalRankMatrix_at_zero, Nat.zero_add]
    rw [diagonal_value_cast ψ (by omega : 0 + (j + k) + 1 = j + k + 1)]

/-- Eventual diagonal convergence transfers to one half-plane for the block integral. -/
theorem converges_on_right_of_finite_expansion (j k m : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)) [SFinite ν]
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
    (Ws : Fin m → WhittakerFunctions ψ (n + (j + k + 1)))
    (hexp : ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
      W.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (Ws i).val (appendIdentity n (j + k + 1) g))
    (hWs : ∀ i, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      Integrable (unequalRankIntegrand ψ abv j k (Ws i) W' s 0) μ)
    (hφ : ∀ i, Integrable (φ i) ν) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      UnequalRankConverges ψ abv j k μ ν W W' s := by
  obtain ⟨a, ha⟩ := finite_common_bound _ hWs
  exact ⟨a, fun s hs => converges_of_finite_expansion ψ abv j k m
    μ ν W W' φ Ws hexp s (ha s hs) hφ⟩

/-- The finite expansion transfers actual rational continuation, on a convergent half-plane. -/
theorem continuation_of_finite_expansion (j k m q : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
    (Ws : Fin m → WhittakerFunctions ψ (n + (j + k + 1)))
    (hexp : ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
      W.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (Ws i).val (appendIdentity n (j + k + 1) g))
    (hWs : ∀ i, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      Integrable (unequalRankIntegrand ψ abv j k (Ws i) W' s 0) μ)
    (hφ : ∀ i, Integrable (φ i) ν)
    (R : Fin m → RationalFunctions)
    (hR : ∀ i, HasRationalContinuation q
      (fun s => ∫ z, unequalRankIntegrand ψ abv j k (Ws i) W' s 0 z ∂μ) (R i)) :
    HasRationalContinuation q (unequalRankIntegral ψ abv j k μ ν W W')
      (∑ i, RatFunc.C (∫ x, φ i x ∂ν) * R i) := by
  apply continuation_of_eq_on_right
    (continuation_linear_combination Finset.univ _ _ R (fun i _ => hR i))
  obtain ⟨a, ha⟩ := finite_common_bound _ hWs
  exact ⟨a, fun s hs => integral_of_finite_expansion ψ abv j k m
    μ ν W W' φ Ws hexp s (ha s hs) hφ⟩

/-- Every continuation of a finitely expanded integral lies in the diagonal Laurent span. -/
theorem continuation_mem_span_of_finite_expansion (j k m q : ℕ) (hq : 1 < q)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
    (Ws : Fin m → WhittakerFunctions ψ (n + (j + k + 1)))
    (hexp : ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
      W.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (Ws i).val (appendIdentity n (j + k + 1) g))
    (hWs : ∀ i, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      Integrable (unequalRankIntegrand ψ abv j k (Ws i) W' s 0) μ)
    (hφ : ∀ i, Integrable (φ i) ν)
    (values : Set RationalFunctions) (R : Fin m → RationalFunctions)
    (hR : ∀ i, HasRationalContinuation q
      (fun s => ∫ z, unequalRankIntegrand ψ abv j k (Ws i) W' s 0 z ∂μ) (R i))
    (hmem : ∀ i, R i ∈ values) (S : RationalFunctions)
    (hS : HasRationalContinuation q (unequalRankIntegral ψ abv j k μ ν W W') S) :
    S ∈ zetaSpan values := by
  rw [hS.unique hq
    (continuation_of_finite_expansion ψ abv j k m q μ ν W W' φ Ws hexp hWs hφ R hR)]
  exact linear_combination_mem_span Finset.univ _ R (fun i _ => hmem i)

end ActualIntegrands

section CoefficientModels

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- Conditional transfer of the first three analytic clauses to actual coefficient models.
Every analytic input here concerns the diagonal functions of the same models. -/
theorem analytic_of_finite_expansion (j k q : ℕ) (hq : 1 < q)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)) [SFinite ν]
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
    (hexp : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ (m : ℕ) (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
        (fs : Fin m → (coefficientModel π ℓ).toSubmodule),
        (∀ i, Integrable (φ i) ν) ∧
        ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
          f.val.val (unequalRankMatrix j k g x) =
            ∑ i, φ i x * (fs i).val.val (appendIdentity n (j + k + 1) g))
    (hconv : ∀ (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ a : ℝ, ∀ s : ℂ, a < s.re →
        Integrable (unequalRankIntegrand ψ abv j k f.val f'.val s 0) μ)
    (values : Set RationalFunctions)
    (hrat : ∀ (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ R : RationalFunctions, HasRationalContinuation q
        (fun s => ∫ z, unequalRankIntegrand ψ abv j k f.val f'.val s 0 z ∂μ) R ∧
        R ∈ values)
    (hdenom : HasCommonDenominator values) :
    (∀ (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ a : ℝ, ∀ s : ℂ, a < s.re →
        UnequalRankConverges ψ abv j k μ ν f.val f'.val s) ∧
    (∀ (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ R : RationalFunctions, HasRationalContinuation q
        (unequalRankModelIntegral ψ abv j k μ ν π σ ℓ ℓ' f f') R) ∧
    HasCommonDenominator (unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ') := by
  classical
  refine ⟨?_, ?_, commonDenominator_of_mem_span hdenom ?_⟩
  · intro f f'
    obtain ⟨m, φ, fs, hφ, he⟩ := hexp f
    exact converges_on_right_of_finite_expansion ψ abv j k m μ ν f.val f'.val
      φ (fun i => (fs i).val) he (fun i => hconv (fs i) f') hφ
  · intro f f'
    obtain ⟨m, φ, fs, hφ, he⟩ := hexp f
    choose R hR hmem using fun i => hrat (fs i) f'
    exact ⟨_, continuation_of_finite_expansion ψ abv j k m q μ ν f.val f'.val
      φ (fun i => (fs i).val) he (fun i => hconv (fs i) f') hφ R hR⟩
  · rintro S ⟨f, f', hS⟩
    obtain ⟨m, φ, fs, hφ, he⟩ := hexp f
    choose R hR hmem using fun i => hrat (fs i) f'
    exact continuation_mem_span_of_finite_expansion ψ abv j k m q hq μ ν f.val f'.val
      φ (fun i => (fs i).val) he (fun i => hconv (fs i) f') hφ values R hR hmem S hS

end CoefficientModels

section ZeroRowModelTransport

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- Transport a representation along an equality of the rank gaps. -/
private def gapRepresentationCast {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V) :
    Representation ℂ (Langlands.GeneralLinear (n + d + 1) F) V := by
  cases h
  exact π

/-- Transport its specified Whittaker functional along the same equality. -/
private def gapFunctionalCast {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (ℓ : glFunctionals ψ (n + e) π) :
    glFunctionals ψ (n + d) (gapRepresentationCast h π) := by
  cases h
  exact ℓ

private theorem gapRepresentationCast_whittakerType {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (hπ : IsOfWhittakerType (n + e) (standardCharacter ψ (n + e)) π) :
    IsOfWhittakerType (n + d) (standardCharacter ψ (n + d))
      (gapRepresentationCast h π) := by
  cases h
  exact hπ

private theorem gapFunctionalCast_ne_zero {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (ℓ : glFunctionals ψ (n + e) π) (hℓ : ℓ.val ≠ 0) :
    (gapFunctionalCast ψ h π ℓ).val ≠ 0 := by
  cases h
  exact hℓ

/-- Transport a coefficient within that same representation and functional. -/
private def gapCoefficientCast {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (ℓ : glFunctionals ψ (n + e) π)
    (f : (coefficientModel π ℓ).toSubmodule) :
    (coefficientModel (gapRepresentationCast h π) (gapFunctionalCast ψ h π ℓ)).toSubmodule := by
  cases h
  exact f

private theorem gapCoefficientCast_diagonal {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (ℓ : glFunctionals ψ (n + e) π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (gapCoefficientCast ψ h π ℓ f).val.val (appendIdentity n d g) =
      f.val.val (appendIdentity n e g) := by
  cases h
  rfl

private theorem zero_row_model_integrand (j k : ℕ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (z : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv 0 (j + k)
        (gapCoefficientCast ψ (by omega : 0 + (j + k) + 1 = j + k + 1) π ℓ f).val
        W' s 0 z =
      unequalRankIntegrand ψ abv j k f.val W' s 0 z := by
  induction z using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk, unequalRankMatrix_at_zero,
      gapCoefficientCast_diagonal, Nat.zero_add]

/-- The zero-row analytic input supplies the diagonal hypotheses on the same models.
The premise uses the actual product convergence and nested integrals. -/
theorem diagonal_analytic_of_zero_row (j k q : ℕ) [MeasurableSpace F]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ) :
    let hgap : 0 + (j + k) + 1 = j + k + 1 := by omega
    let π₀ := gapRepresentationCast hgap π
    let ℓ₀ := gapFunctionalCast ψ hgap π ℓ
    (∀ (f : (coefficientModel π₀ ℓ₀).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ a : ℝ, ∀ s : ℂ, a < s.re →
        UnequalRankConverges ψ abv 0 (j + k) μ (rectangularMeasure ν 0 (n + 1))
          f.val f'.val s) →
    (∀ (f : (coefficientModel π₀ ℓ₀).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ R : RationalFunctions, HasRationalContinuation q
        (unequalRankModelIntegral ψ abv 0 (j + k) μ (rectangularMeasure ν 0 (n + 1))
          π₀ σ ℓ₀ ℓ' f f') R) →
    HasCommonDenominator (unequalRankRationalValues 0 (j + k) q ψ abv
      μ (rectangularMeasure ν 0 (n + 1)) π₀ σ ℓ₀ ℓ') →
    ∃ values : Set RationalFunctions,
      (∀ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule),
        ∃ a : ℝ, ∀ s : ℂ, a < s.re →
          Integrable (unequalRankIntegrand ψ abv j k f.val f'.val s 0) μ) ∧
      (∀ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule),
        ∃ R : RationalFunctions, HasRationalContinuation q
          (fun s => ∫ z, unequalRankIntegrand ψ abv j k f.val f'.val s 0 z ∂μ) R ∧
          R ∈ values) ∧
      HasCommonDenominator values := by
  intro hgap π₀ ℓ₀ hconv hrat hdenom
  refine ⟨unequalRankRationalValues 0 (j + k) q ψ abv
    μ (rectangularMeasure ν 0 (n + 1)) π₀ σ ℓ₀ ℓ', ?_, ?_, hdenom⟩
  · intro f f'
    let f₀ := gapCoefficientCast ψ hgap π ℓ f
    obtain ⟨a, ha⟩ := hconv f₀ f'
    refine ⟨a, fun s hs => ?_⟩
    have hi := (UnequalRankZeroRowAssembly.zero_row_converges_iff ψ abv (j + k) μ ν f₀.val f'.val s).mp (ha s hs)
    have he : unequalRankIntegrand ψ abv 0 (j + k) f₀.val f'.val s 0 =
        unequalRankIntegrand ψ abv j k f.val f'.val s 0 :=
      funext (zero_row_model_integrand ψ abv j k π ℓ f f'.val s)
    rw [he] at hi
    exact hi
  · intro f f'
    let f₀ := gapCoefficientCast ψ hgap π ℓ f
    obtain ⟨R, hR⟩ := hrat f₀ f'
    refine ⟨R, ?_, ⟨f₀, f', hR⟩⟩
    have he : unequalRankModelIntegral ψ abv 0 (j + k) μ
        (rectangularMeasure ν 0 (n + 1)) π₀ σ ℓ₀ ℓ' f₀ f' =
        (fun s => ∫ z, unequalRankIntegrand ψ abv j k f.val f'.val s 0 z ∂μ) := by
      funext s
      rw [unequalRankModelIntegral, UnequalRankZeroRowAssembly.zero_row_integral_eq]
      simp only [f₀, zero_row_model_integrand]
    rw [he] at hR
    exact hR


end ZeroRowModelTransport

/-- Every rectangular Schwartz function is integrable for the supplied product Haar measure. -/
theorem rectangular_schwartz_integrable {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    [IsTopologicalAddGroup F] [SecondCountableTopology F]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (j t : ℕ)
    (φ : SchwartzBruhat (Matrix (Fin j) (Fin t) F)) :
    Integrable (φ : Matrix (Fin j) (Fin t) F → ℂ) (rectangularMeasure ν j t) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- The same integrability statement in the parent's supplied p-adic topology. -/
theorem padic_rectangular_schwartz_integrable {p : ℕ} [Fact p.Prime]
    (F : PadicField p) (T : F.TopologicalData) (j t : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ (ν : AdditiveHaarMeasure F.Carrier)
      (φ : SchwartzBruhat (Matrix (Fin j) (Fin t) F.Carrier)),
      Integrable (φ : Matrix (Fin j) (Fin t) F.Carrier → ℂ)
        (rectangularMeasure ν j t) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ν φ
  exact rectangular_schwartz_integrable ν j t φ

/-- Assembly of all four clauses from the two remaining analytic and
representation-theoretic prerequisites. Compact support, finite expansion and
algebraic normalization are imported proofs, not additional premises. -/
theorem unequalRankAnalytic_of_prerequisites.{uF,uV,uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ)
    (hzero : UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n (j + k))
    (hunit : UnequalRankUnitSpanStatement.{uF,uV,uW} F T n j k) :
    UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (GeneralLinear.upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  let hgap : 0 + (j + k) + 1 = j + k + 1 := by omega
  let π₀ := gapRepresentationCast hgap π
  let ℓ₀ := gapFunctionalCast ψ hgap π ℓ
  obtain ⟨hc₀, hr₀, hd₀⟩ :=
    hzero ψ μ hμ ν V W π₀ σ
      (gapRepresentationCast_whittakerType ψ hgap π hπ) hσ ℓ₀ ℓ'
      (gapFunctionalCast_ne_zero ψ hgap π ℓ hℓ) hℓ'
  obtain ⟨values, hc, hr, hd⟩ :=
    diagonal_analytic_of_zero_row ψ (normalizedAbsoluteValue T)
      j k T.residueCardinality μ ν π σ ℓ ℓ' hc₀ hr₀ hd₀
  have hexp : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ (m : ℕ)
        (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F.Carrier → ℂ)
        (fs : Fin m → (coefficientModel π ℓ).toSubmodule),
        (∀ i, Integrable (φ i) (rectangularMeasure ν j (n + 1))) ∧
        ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) x,
          f.val.val (unequalRankMatrix j k g x) =
            ∑ i, φ i x * (fs i).val.val (appendIdentity n (j + k + 1) g) := by
    intro f
    obtain ⟨m, φ, fs, he⟩ := unequalRankFiniteExpansion F T n j k
      ψ V π hπ ℓ hℓ f
      (unequalRankCompactSupport.{uF,uV} F T n j k ψ V π hπ ℓ hℓ f)
    exact ⟨m, fun i => (φ i : Matrix (Fin j) (Fin (n + 1)) F.Carrier → ℂ),
      fs, fun i => padic_rectangular_schwartz_integrable F T j (n + 1) ν (φ i), he⟩
  obtain ⟨hconv, hrat, hden⟩ :=
    analytic_of_finite_expansion ψ (normalizedAbsoluteValue T)
      j k T.residueCardinality T.residueCardinality_gt_one
      μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ' hexp hc values hr hd
  exact ⟨hconv, hrat, hden,
    normalizedGeneratorExistence _ hden (hunit ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ')⟩

/-- The published unit-span theorem leaves only zero-row analytics as an input
to the complete unequal-rank analytic conclusion. -/
theorem unequalRankAnalytic_of_zero_row.{uF,uV,uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ)
    (hzero : UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n (j + k)) :
    UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k :=
  unequalRankAnalytic_of_prerequisites F T n j k hzero
    (unequalRankUnitSpan.{uF,uV,uW} F T n j k)

end UnequalRankReduction

/-- JPSS Theorem 2.7(i)-(ii) for every unequal-rank block, with the supplied
topology and measures and independent representation universes. -/
theorem unequalRankAnalytic.{uF,uV,uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ) :
    UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k :=
  UnequalRankReduction.unequalRankAnalytic_of_zero_row.{uF,uV,uW} F T n j k
    (unequalRankZeroRowAnalytic.{uF,uV,uW} F T n (j + k))

end Langlands.RankinSelberg
