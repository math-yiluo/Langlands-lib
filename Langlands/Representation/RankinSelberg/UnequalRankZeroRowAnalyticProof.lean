import Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticStatement
import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
import Langlands.Representation.RankinSelberg.QuotientRootIntegrationProof
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityProof
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.Representation.Whittaker.TypeAsymptoticProof
import Langlands.Representation.RankinSelberg.ModelAsymptoticProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowNormalizedCompactIntegrationProof

/-!
# Zero-row unequal-rank convergence, rationality and a uniform denominator

Assemble full-torus expansions, normalized compact averages and finite-function
Mellin analysis, then transport through quotient Iwasawa integration and the
zero-row Dirac measure.
The two Dirac reductions are reused from Worker 329's shared revision-3 draft.
-/

noncomputable section

namespace Langlands.RankinSelberg
namespace UnequalRankZeroRowAssembly

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open RationalContinuationLinear
open scoped BigOperators

universe uF uV uW

section ZeroRows

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}

/-- Zero-row convergence is exactly integrability of the diagonal quotient function. -/
theorem zero_row_converges_iff (k : ℕ) [MeasurableSpace F]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    UnequalRankConverges ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' s ↔
      Integrable (unequalRankIntegrand ψ abv 0 k W W' s 0) μ := by
  unfold UnequalRankConverges
  rw [rectangularMeasure_zero_rows]
  constructor
  · intro h
    simpa only [integral_dirac] using h.integral_prod_left
  · intro h
    have hc : Integrable (fun _ : Matrix (Fin 0) (Fin (n + 1)) F => (1 : ℂ))
        (Measure.dirac 0) := integrable_const 1
    apply (h.mul_prod hc).congr
    filter_upwards [] with qx
    rw [mul_one, Subsingleton.elim qx.2 0]

/-- The actual zero-row nested integral is the diagonal quotient integral. -/
theorem zero_row_integral_eq (k : ℕ) [MeasurableSpace F]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' s =
      ∫ q, unequalRankIntegrand ψ abv 0 k W W' s 0 q ∂μ := by
  simp only [unequalRankIntegral, rectangularMeasure_zero_rows, integral_dirac]

end ZeroRows

/-- A finite compact average remains a finite average after multiplying by a
fixed root weight and substituting the pointwise expansion at its representatives. -/
private theorem weighted_compact_formulas
    {β : Type*} [MeasurableSpace β] (κ : Measure β)
    (H : β → ℂ) {r : ℕ} (z : Fin r → β) (c : Fin r → ℝ)
    (w : ℂ) (S : Fin r → ℂ)
    (hi : Integrable H κ)
    (hsum : (∫ u, H u ∂κ) = ∑ t, (c t : ℂ) * H (z t))
    (habs : (∫⁻ u, ‖H u‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖H (z t)‖ₑ)
    (hpoint : ∀ t, H (z t) * w = S t) :
    Integrable (fun u => H u * w) κ ∧
    (∫ u, H u * w ∂κ) = ∑ t, (c t : ℂ) * S t ∧
    (∫⁻ u, ‖H u * w‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
  refine ⟨hi.mul_const w, ?_, ?_⟩
  · rw [integral_mul_const, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, hpoint]
  · calc
      (∫⁻ u, ‖H u * w‖ₑ ∂κ) = (∫⁻ u, ‖H u‖ₑ ∂κ) * ‖w‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_mul_const' _ _ enorm_ne_top
      _ = (∑ t, ENNReal.ofReal (c t) * ‖H (z t)‖ₑ) * ‖w‖ₑ := by rw [habs]
      _ = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_assoc, ← enorm_mul, hpoint]

/-- A fixed finite-function family and finite compact-average formulas imply
root convergence and continuation with the same denominator for every index. -/
private theorem root_analytic_of_finite_formulas {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (hM : FiniteFunctionMellinStatement.{uF}) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    let A := Fin (n + 1) → F.Carrierˣ
    let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
    let v : A → ℂ → ℂ := fun a s =>
      ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
    let I := fun (η : A → ℂ) (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (s : ℂ) (a : A) => Ψ (fun i => (a i : F.Carrier)) * η a * v a s
    ∀ (ι : Type uV) (β : Type uW) [MeasurableSpace β] (κ : Measure β)
      (H : ι → ℂ → A → β → ℂ) (m : ℕ) (η : Fin m → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) →
      (∀ x, ∃ (r : ℕ) (c : Fin r → ℝ)
        (Ψ : Fin r → Fin m → SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        ∀ a s,
          (∫ z, H x s a z ∂κ) = ∑ t, (c t : ℂ) * ∑ j, I (η j) (Ψ t j) s a ∧
          (∫⁻ z, ‖H x s a z‖ₑ ∂κ) =
            ∑ t, ENNReal.ofReal (c t) * ‖∑ j, I (η j) (Ψ t j) s a‖ₑ) →
      ∃ D : LaurentCoefficients, D ≠ 0 ∧
        (∀ x, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
          Integrable (fun a => ∫ z, H x s a z ∂κ) dA ∧
          (∫⁻ a, ∫⁻ z, ‖H x s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
        (∀ x, ∃ R : RationalFunctions,
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, ∫ z, H x s a z ∂κ ∂dA) R) ∧
        (∀ x (R : RationalFunctions),
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, ∫ z, H x s a z ∂κ ∂dA) R →
          ∃ P : LaurentCoefficients, laurentToRatFunc P = laurentToRatFunc D * R) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let v : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  let I := fun (η : A → ℂ) (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
    (s : ℂ) (a : A) => Ψ (fun i => (a i : F.Carrier)) * η a * v a s
  dsimp only
  intro ι β _ κ H m η hη hexp
  let X : Finset (A → ℂ) := Finset.univ.image η
  have hX (e : A → ℂ) (he : e ∈ X) : Continuous e ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : A => fun a : A => e (b * a))) := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    exact hη j
  have hmem (j : Fin m) : η j ∈ X := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hM' := hM p inferInstance F T (n + 1) (fun i => i.val + 1)
    (fun _ => Nat.zero_lt_succ _) X hX
  simp only [Nat.cast_add, Nat.cast_one] at hM'
  change (∀ e ∈ X, ∀ Ψ, ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I e Ψ s) dA) ∧
    (∀ e ∈ X, ∀ Ψ, ∃ R : RationalFunctions,
      HasRationalContinuation T.residueCardinality (fun s => ∫ a, I e Ψ s a ∂dA) R) ∧
    HasCommonDenominator {R | ∃ e ∈ X, ∃ Ψ,
      HasRationalContinuation T.residueCardinality (fun s => ∫ a, I e Ψ s a ∂dA) R} at hM'
  let values : Set RationalFunctions := {R | ∃ e ∈ X, ∃ Ψ,
    HasRationalContinuation T.residueCardinality (fun s => ∫ a, I e Ψ s a ∂dA) R}
  obtain ⟨hconv, hrat, D, hD, hclear⟩ := hM'
  refine ⟨D, hD, ?_⟩
  let B := fun (x : ι) s a => ∫ z, H x s a z ∂κ
  let J := fun x s => ∫ a, B x s a ∂dA
  have hdata (x : ι) :
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (B x s) dA ∧
        (∫⁻ a, ∫⁻ z, ‖H x s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      ∃ R : RationalFunctions, HasRationalContinuation T.residueCardinality (J x) R ∧
        R ∈ zetaSpan values := by
    obtain ⟨r, c, Ψ, hformula⟩ := hexp x
    let S := fun (t : Fin r) (s : ℂ) (a : A) => ∑ j, I (η j) (Ψ t j) s a
    have hB (s : ℂ) (a : A) : B x s a = ∑ t, (c t : ℂ) * S t s a :=
      (hformula a s).1
    have habs (s : ℂ) (a : A) :
        (∫⁻ z, ‖H x s a z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t s a‖ₑ :=
      (hformula a s).2
    choose b hb using fun (t : Fin r) (j : Fin m) => hconv (η j) (hmem j) (Ψ t j)
    obtain ⟨b₀, hb₀⟩ := (Set.finite_range (fun tj : Fin r × Fin m => b tj.1 tj.2)).bddAbove
    have hI (s : ℂ) (hs : b₀ < s.re) (t : Fin r) (j : Fin m) :
        Integrable (I (η j) (Ψ t j) s) dA :=
      hb t j s ((hb₀ (Set.mem_range_self (t, j))).trans_lt hs)
    have hS (s : ℂ) (hs : b₀ < s.re) (t : Fin r) : Integrable (S t s) dA :=
      integrable_finsetSum _ (fun j _ => hI s hs t j)
    have hJ (s : ℂ) (hs : b₀ < s.re) :
        J x s = ∑ t, (c t : ℂ) * ∑ j, ∫ a, I (η j) (Ψ t j) s a ∂dA := by
      change (∫ a, B x s a ∂dA) = _
      simp_rw [hB]
      rw [integral_finsetSum _ (fun t _ => (hS s hs t).const_mul (c t : ℂ))]
      apply Finset.sum_congr rfl
      intro t _
      rw [integral_const_mul]
      congr 1
      exact integral_finsetSum _ (fun j _ => hI s hs t j)
    refine ⟨⟨b₀, ?_⟩, ?_⟩
    · intro s hs
      constructor
      · simp_rw [show B x s = fun a => ∑ t, (c t : ℂ) * S t s a from funext (hB s)]
        exact integrable_finsetSum _ (fun t _ => (hS s hs t).const_mul (c t : ℂ))
      · simp_rw [habs]
        rw [lintegral_finsetSum' Finset.univ
          (f := fun t a => ENNReal.ofReal (c t) * ‖S t s a‖ₑ)
          (fun t _ => aemeasurable_const.mul (hS s hs t).aestronglyMeasurable.enorm)]
        apply ENNReal.sum_lt_top.mpr
        intro t _
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (hasFiniteIntegral_iff_enorm.mp (hS s hs t).hasFiniteIntegral)
    · choose R hR using fun (t : Fin r) (j : Fin m) => hrat (η j) (hmem j) (Ψ t j)
      refine ⟨∑ t, RatFunc.C (c t : ℂ) * ∑ j, R t j, ?_, ?_⟩
      · apply continuation_of_eq_on_right
          (continuation_linear_combination Finset.univ (fun t => (c t : ℂ))
            (fun t s => ∑ j, ∫ a, I (η j) (Ψ t j) s a ∂dA)
            (fun t => ∑ j, R t j) (fun t _ =>
              continuation_sum Finset.univ _ (R t) (fun j _ => hR t j)))
        exact ⟨b₀, hJ⟩
      · apply Submodule.sum_mem
        intro t _
        have hsum : (∑ j, R t j) ∈ zetaSpan values := by
          apply Submodule.sum_mem
          intro j _
          exact mem_zetaSpan ⟨η j, hmem j, Ψ t j, hR t j⟩
        have hsmul := Submodule.smul_mem (zetaSpan values)
          (LaurentPolynomial.C (c t : ℂ)) hsum
        simpa only [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C] using hsmul
  refine ⟨fun x => (hdata x).1, ?_, ?_⟩
  · intro x
    obtain ⟨R, hR, _⟩ := (hdata x).2
    exact ⟨R, hR⟩
  · intro x R hR
    obtain ⟨S, hS, hspan⟩ := (hdata x).2
    have heq : R = S := hR.unique T.residueCardinality_gt_one hS
    subst R
    exact denominator_clears_span D hclear hspan


/-- Transport compact root-average analytic data to the actual zero-row
product-measure integrals. -/
private theorem analytic_of_root_average {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
    ∀ (ν : AdditiveHaarMeasure F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsSmooth π → IsSmooth σ →
    ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ),
      let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
      let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
      let A := Fin (n + 1) → F.Carrierˣ
      let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
      let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
      let w : A → ℂ := fun a =>
        (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
          ((i.val + 1) * (n - i.val)))⁻¹
      let H := fun (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule) (s : ℂ) (a : A)
        (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
        unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
          (Iwasawa.diagonalUnits (d a) * z) * w a
      let J := fun f f' s => ∫ a, ∫ z, H f f' s a z ∂κ ∂dA
      ∀ D : LaurentCoefficients, D ≠ 0 →
      (∀ f f', ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        (∫⁻ a, ∫⁻ z, ‖H f f' s a z‖ₑ ∂κ ∂dA) < ⊤) →
      (∀ f f', ∃ R : RationalFunctions,
        HasRationalContinuation T.residueCardinality (J f f') R) →
      (∀ f f' (R : RationalFunctions),
        HasRationalContinuation T.residueCardinality (J f f') R →
        ∃ P : LaurentCoefficients, laurentToRatFunc P = laurentToRatFunc D * R) →
      (∀ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule), ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        UnequalRankConverges ψ (normalizedAbsoluteValue T) 0 k
          μ (rectangularMeasure ν 0 (n + 1)) f.val f'.val s) ∧
      (∀ f f', ∃ R : RationalFunctions,
        HasRationalContinuation T.residueCardinality
          (unequalRankModelIntegral ψ (normalizedAbsoluteValue T) 0 k
            μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f') R) ∧
      HasCommonDenominator
        (unequalRankRationalValues 0 k T.residueCardinality ψ
          (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ') := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ hright μ hμ ν V _ _ W _ _ π σ hsπ hsσ ℓ ℓ'
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let H := fun (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule) (s : ℂ) (a : A)
    (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
    unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
      (Iwasawa.diagonalUnits (d a) * z) * w a
  let J := fun f f' s => ∫ a, ∫ z, H f f' s a z ∂κ ∂dA
  dsimp only
  intro D hD hconv hrat hclear
  have hmeas (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule) (s : ℂ) :
      Measurable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
        f.val f'.val s 0) :=
    (unequalRankZeroRowIntegrandContinuous F.Carrier n k (normalizedAbsoluteValue T)
      (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
      V W π σ hsπ hsσ ψ ℓ ℓ' f f' s).measurable
  have htransport (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule) (s : ℂ) :
      (Integrable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
        f.val f'.val s 0) μ ↔
        (∫⁻ a, ∫⁻ z, ‖H f f' s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      (Integrable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
        f.val f'.val s 0) μ →
        (∫ q, unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
          f.val f'.val s 0 q ∂μ) = J f f' s) :=
    (quotientRootIntegration F T n (quotientIwasawaIntegration F T n) μ hμ).2
      (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0)
      (hmeas f f' s)
  have hdata (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule) :
      ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        UnequalRankConverges ψ (normalizedAbsoluteValue T) 0 k
          μ (rectangularMeasure ν 0 (n + 1)) f.val f'.val s ∧
        unequalRankModelIntegral ψ (normalizedAbsoluteValue T) 0 k
          μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f' s = J f f' s := by
    obtain ⟨b, hb⟩ := hconv f f'
    refine ⟨b, fun s hs => ?_⟩
    have hc := (htransport f f' s).1.mpr (hb s hs)
    constructor
    · exact (zero_row_converges_iff ψ (normalizedAbsoluteValue T) k
        μ ν f.val f'.val s).mpr hc
    · change unequalRankIntegral _ _ _ _ _ _ _ _ _ = _
      rw [zero_row_integral_eq]
      exact (htransport f f' s).2 hc
  refine ⟨?_, ?_, D, hD, ?_⟩
  · intro f f'
    obtain ⟨b, hb⟩ := hdata f f'
    exact ⟨b, fun s hs => (hb s hs).1⟩
  · intro f f'
    obtain ⟨R, hR⟩ := hrat f f'
    obtain ⟨b, hb⟩ := hdata f f'
    exact ⟨R, continuation_of_eq_on_right hR ⟨b, fun s hs => (hb s hs).2⟩⟩
  · intro R hR
    obtain ⟨f, f', hR⟩ := hR
    obtain ⟨b, hb⟩ := hdata f f'
    exact hclear f f' R
      (continuation_of_eq_on_right hR ⟨b, fun s hs => (hb s hs).2.symm⟩)

end UnequalRankZeroRowAssembly

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

/-- Assemble the zero-row conclusion from full-torus expansions and Mellin analysis. -/
private theorem unequalRankZeroRowAnalytic_of_analytic_inputs
    (hAV : WhittakerTypeAsymptoticStatement.{uF, uV})
    (hAW : WhittakerTypeAsymptoticStatement.{uF, uW})
    (hM : FiniteFunctionMellinStatement.{uF})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n k : ℕ) :
    UnequalRankZeroRowAnalyticStatement.{uF, uV, uW} F T n k := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' _ _
  have hEπ : CoefficientTorusExpansion
      (standardCharacter ψ (n + (0 + k + 1))) π :=
    modelAsymptoticTransfer hAV p inferInstance F T (n + (0 + k + 1))
      V π ψ _ (Or.inl rfl) hπ
  have hEσ : CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ :=
    modelAsymptoticTransfer hAW p inferInstance F T n W σ ψ _ (Or.inr rfl) hσ
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let v : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  let I := fun (η : A → ℂ) (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
    (s : ℂ) (a : A) => Ψ (fun i => (a i : F.Carrier)) * η a * v a s
  let C := (coefficientModel π ℓ).toSubmodule
  let C' := (coefficientModel σ ℓ').toSubmodule
  let H := fun (x : C × C') (s : ℂ) (a : A)
    (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
    unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k x.1.val x.2.val s 0
      (Iwasawa.diagonalUnits (d a) * z) * w a
  obtain ⟨m, η, hη, hexp⟩ :=
    unequalRankZeroRowRootExpansion F T n k V W π σ ψ hEπ hEσ
  have hform : ∀ x : C × C', ∃ (r : ℕ) (c : Fin r → ℝ)
      (Ψ : Fin r → Fin m → SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      ∀ a s,
        (∫ z, H x s a z ∂κ) = ∑ t, (c t : ℂ) * ∑ j, I (η j) (Ψ t j) s a ∧
        (∫⁻ z, ‖H x s a z‖ₑ ∂κ) =
          ∑ t, ENNReal.ofReal (c t) * ‖∑ j, I (η j) (Ψ t j) s a‖ₑ := by
    intro x
    obtain ⟨r, z, c, _, _, havg⟩ :=
      unequalRankZeroRowNormalizedCompactIntegration F T n k V W π σ
        hπ.1.1 hσ.1.1 ψ ℓ ℓ' x.1 x.2
    choose Ψ hΨ using fun t : Fin r => hexp ℓ ℓ' x.1 x.2 (z t)
    refine ⟨r, c, Ψ, ?_⟩
    intro a s
    obtain ⟨hi, hsum, habs⟩ := havg (Iwasawa.diagonalUnits (d a)) s
    exact (UnequalRankZeroRowAssembly.weighted_compact_formulas κ
      (fun u => unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k
        x.1.val x.2.val s 0 (Iwasawa.diagonalUnits (d a) * u))
      (fun t => (z t).val) c (w a) (fun t => ∑ j, I (η j) (Ψ t j) s a)
      hi hsum habs (fun t => hΨ t a s)).2
  obtain ⟨D, hD, hconv, hrat, hclear⟩ :=
    UnequalRankZeroRowAssembly.root_analytic_of_finite_formulas F T n hM
      (C × C') (Langlands.GeneralLinear (n + 1) F.Carrier) κ H m η hη hform
  apply UnequalRankZeroRowAssembly.analytic_of_root_average F T n k
    ψ μ hμ ν V W π σ hπ.1.1 hσ.1.1 ℓ ℓ' D hD
  · intro f f'
    obtain ⟨b, hb⟩ := hconv (f, f')
    exact ⟨b, fun s hs => (hb s hs).2⟩
  · intro f f'
    exact hrat (f, f')
  · intro f f'
    exact hclear (f, f')

/-- Zero-row unequal-rank absolute convergence, rational continuation and one
Laurent denominator for all coefficient pairs, for every positive rank gap. -/
theorem unequalRankZeroRowAnalytic.{uF, uV, uW}
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n k : ℕ) :
    UnequalRankZeroRowAnalyticStatement.{uF, uV, uW} F T n k :=
  unequalRankZeroRowAnalytic_of_analytic_inputs
    Langlands.whittakerTypeAsymptotic.{uF, uV}
    Langlands.whittakerTypeAsymptotic.{uF, uW}
    finiteFunctionMellin.{uF} F T n k

end Langlands.RankinSelberg
