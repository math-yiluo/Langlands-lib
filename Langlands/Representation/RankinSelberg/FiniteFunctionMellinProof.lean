import Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement
import Langlands.Representation.RankinSelberg.FiniteFunctionTensorProof
import Langlands.Representation.RankinSelberg.OneVariableMellinProof
import Langlands.HarmonicAnalysis.RowTensorDecompositionProof
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Polynomial
open scoped BigOperators

namespace MellinAssembly

universe u

theorem localHaar_sigmaFinite {p : ℕ} [Fact p.Prime]
    (F : PadicField p) (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    SigmaFinite (localMultiplicativeHaar F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := T.fieldT2
  let := T.secondCountableTopology
  let : SecondCountableTopology F.Carrierˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  unfold localMultiplicativeHaar multiplicativeHaar normalizedCompactOpenHaar
  infer_instance

theorem field_totallyDisconnected {p : ℕ} [Fact p.Prime]
    (F : PadicField p) (T : F.TopologicalData) :
    letI := T.topology
    TotallyDisconnectedSpace F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  infer_instance

theorem uniform_right {ι : Type*} [Finite ι] (P : ι → ℂ → Prop)
    (h : ∀ i, ∃ c : ℝ, ∀ s : ℂ, c < s.re → P i s) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re → ∀ i, P i s := by
  classical
  choose c hc using h
  obtain ⟨b, hb⟩ := (Set.finite_range c).bddAbove
  exact ⟨b, fun s hs i => hc i s ((hb (Set.mem_range_self i)).trans_lt hs)⟩

private theorem denom_eval_mul_ne_zero {R S : RationalFunctions} {x : ℂ}
    (hR : R.denom.eval x ≠ 0) (hS : S.denom.eval x ≠ 0) :
    (R * S).denom.eval x ≠ 0 := by
  intro h0
  have h := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) x
    (RatFunc.denom_mul_dvd R S) h0
  simp only [eval₂_id, eval_mul, mul_eq_zero, hR, hS, or_self] at h

theorem continuation_mul {q : ℕ} {f g : ℂ → ℂ} {R S : RationalFunctions}
    (hR : HasRationalContinuation q f R) (hS : HasRationalContinuation q g S) :
    HasRationalContinuation q (fun s => f s * g s) (R * S) := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hS
  refine ⟨max a b, fun s hs => ?_⟩
  obtain ⟨hdR, heR⟩ := ha s ((le_max_left a b).trans_lt hs)
  obtain ⟨hdS, heS⟩ := hb s ((le_max_right a b).trans_lt hs)
  exact ⟨denom_eval_mul_ne_zero hdR hdS,
    (congrArg₂ (· * ·) heR heS).trans (RatFunc.eval_mul _ _ hdR hdS).symm⟩

theorem continuation_prod {ι : Type*} {q : ℕ} (t : Finset ι)
    (f : ι → ℂ → ℂ) (R : ι → RationalFunctions)
    (h : ∀ i ∈ t, HasRationalContinuation q (f i) (R i)) :
    HasRationalContinuation q (fun s => ∏ i ∈ t, f i s) (∏ i ∈ t, R i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp [RatFunc.denom_one]⟩
  | @insert i t hi ih =>
    have hprod := continuation_mul (h i (Finset.mem_insert_self i t))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.prod_insert hi] using hprod

theorem commonDenominator_iUnion {ι : Type*} [Fintype ι]
    (S : ι → Set RationalFunctions) (h : ∀ i, HasCommonDenominator (S i)) :
    HasCommonDenominator (⋃ i, S i) := by
  classical
  choose d hd hclear using h
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr (fun i _ => hd i), ?_⟩
  intro R hR
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hR
  obtain ⟨P, hP⟩ := hclear i R hi
  obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  refine ⟨e * P, ?_⟩
  rw [map_mul, hP, he, map_mul]
  ring

theorem commonDenominator_products {ι : Type*} [Fintype ι]
    (S : ι → Set RationalFunctions) (h : ∀ i, HasCommonDenominator (S i)) :
    HasCommonDenominator {R | ∃ f : ι → RationalFunctions,
      (∀ i, f i ∈ S i) ∧ R = ∏ i, f i} := by
  classical
  choose d hd hclear using h
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr (fun i _ => hd i), ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  choose P hP using fun i => hclear i (f i) (hf i)
  refine ⟨∏ i, P i, ?_⟩
  simp only [map_prod, hP, Finset.prod_mul_distrib]

theorem commonDenominator_subset {S U : Set RationalFunctions}
    (h : HasCommonDenominator S) (hUS : U ⊆ S) : HasCommonDenominator U := by
  obtain ⟨d, hd, hclear⟩ := h
  exact ⟨d, hd, fun R hR => hclear R (hUS hR)⟩

theorem sum_prod_analytic {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : κ → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (q : ℕ) (c : ι → ℂ) (f : ι → (i : κ) → ℂ → E i → ℂ)
    (R : ι → κ → RationalFunctions)
    (hint : ∀ j i, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      Integrable (f j i s) (μ i))
    (hcont : ∀ j i, HasRationalContinuation q (fun s => ∫ a, f j i s a ∂μ i) (R j i)) :
    (∃ b : ℝ, ∀ s : ℂ, b < s.re →
      Integrable (fun a : ∀ i, E i => ∑ j, c j * ∏ i, f j i s (a i)) (Measure.pi μ)) ∧
    HasRationalContinuation q
      (fun s => ∫ a : ∀ i, E i, ∑ j, c j * ∏ i, f j i s (a i) ∂Measure.pi μ)
      (∑ j, RatFunc.C (c j) * ∏ i, R j i) := by
  classical
  obtain ⟨b, hb⟩ := uniform_right
    (fun ji : ι × κ => fun s => Integrable (f ji.1 ji.2 s) (μ ji.2))
    (fun ji => hint ji.1 ji.2)
  have hprod (s : ℂ) (hs : b < s.re) (j : ι) :
      Integrable (fun a : ∀ i, E i => c j * ∏ i, f j i s (a i)) (Measure.pi μ) :=
    (Integrable.fintype_prod_dep (fun i => hb s hs (j, i))).const_mul (c j)
  refine ⟨⟨b, fun s hs => integrable_finsetSum _ (fun j _ => hprod s hs j)⟩, ?_⟩
  apply RationalContinuationLinear.continuation_of_eq_on_right
    (RationalContinuationLinear.continuation_linear_combination Finset.univ c _
      (fun j => ∏ i, R j i)
      (fun j _ => continuation_prod Finset.univ _ _ (fun i _ => hcont j i)))
  refine ⟨b, fun s hs => ?_⟩
  rw [integral_finsetSum _ (fun j _ => hprod s hs j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_fintype_prod_eq_prod]

theorem tensor_expansion_identity {ι κ ν G : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (c : ι → ℂ) (d : κ → ℂ) (f : ι → ν → G → ℂ)
    (φ : κ → ν → G → ℂ) (w : ν → G → ℂ) (a : ν → G) :
    (∑ k, d k * ∏ i, φ k i (a i)) *
        (∑ j, c j * ∏ i, f j i (a i)) * (∏ i, w i (a i)) =
      ∑ jk : ι × κ, (d jk.2 * c jk.1) *
        ∏ i, (φ jk.2 i (a i) * f jk.1 i (a i) * w i (a i)) := by
  simp only [Fintype.sum_prod_type, Finset.prod_mul_distrib]
  rw [mul_comm (∑ k, _), Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem mellin_of_expansions {G P Q : Type*} [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ] (q : ℕ) (hq : 1 < q)
    (r n : ℕ) (η : (Fin r → G) → ℂ) (c : Fin n → ℂ)
    (f : Fin n → Fin r → G → ℂ)
    (hη : ∀ a, η a = ∑ j, c j * ∏ i, f j i (a i))
    (test : P → (Fin r → G) → ℂ) (localTest : Q → G → ℂ)
    (htest : ∀ Φ : P, ∃ N : ℕ, ∃ d : Fin N → ℂ, ∃ φ : Fin N → Fin r → Q,
      ∀ a, test Φ a = ∑ k, d k * ∏ i, localTest (φ k i) (a i))
    (w : Fin r → ℂ → G → ℂ)
    (hint : ∀ j i (φ : Q), ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      Integrable (fun a => localTest φ a * f j i a * w i s a) μ)
    (hcont : ∀ j i (φ : Q), ∃ R : RationalFunctions,
      HasRationalContinuation q
        (fun s => ∫ a, localTest φ a * f j i a * w i s a ∂μ) R)
    (hden : ∀ j i, HasCommonDenominator {R | ∃ φ : Q,
      HasRationalContinuation q
        (fun s => ∫ a, localTest φ a * f j i a * w i s a ∂μ) R}) :
    let I := fun Φ s a => test Φ a * η a * ∏ i, w i s (a i)
    let M := fun Φ s => ∫ a, I Φ s a ∂Measure.pi (fun _ : Fin r => μ)
    (∀ Φ, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      Integrable (I Φ s) (Measure.pi (fun _ : Fin r => μ))) ∧
    (∀ Φ, ∃ R, HasRationalContinuation q (M Φ) R) ∧
    HasCommonDenominator {R | ∃ Φ, HasRationalContinuation q (M Φ) R} := by
  classical
  dsimp only
  let S (j : Fin n) (i : Fin r) : Set RationalFunctions :=
    {R | ∃ φ : Q, HasRationalContinuation q
      (fun s => ∫ a, localTest φ a * f j i a * w i s a ∂μ) R}
  let V (j : Fin n) : Set RationalFunctions :=
    {R | ∃ g : Fin r → RationalFunctions, (∀ i, g i ∈ S j i) ∧ R = ∏ i, g i}
  have hV : HasCommonDenominator (⋃ j, V j) :=
    commonDenominator_iUnion V (fun j => commonDenominator_products (S j) (hden j))
  have hΦ (Φ : P) :
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable
        (fun a => test Φ a * η a * ∏ i, w i s (a i))
        (Measure.pi (fun _ : Fin r => μ))) ∧
      ∃ R, HasRationalContinuation q
        (fun s => ∫ a, test Φ a * η a * ∏ i, w i s (a i)
          ∂Measure.pi (fun _ : Fin r => μ)) R ∧ R ∈ zetaSpan (⋃ j, V j) := by
    obtain ⟨N, d, φ, hφ⟩ := htest Φ
    choose R hR using fun (jk : Fin n × Fin N) i => hcont jk.1 i (φ jk.2 i)
    have he (s : ℂ) (a : Fin r → G) :
        test Φ a * η a * ∏ i, w i s (a i) =
        ∑ jk : Fin n × Fin N, (d jk.2 * c jk.1) *
          ∏ i, (localTest (φ jk.2 i) (a i) * f jk.1 i (a i) * w i s (a i)) := by
      rw [hφ a, hη a]
      exact tensor_expansion_identity c d f (fun k i => localTest (φ k i))
        (fun i => w i s) a
    obtain ⟨hi, hc⟩ := sum_prod_analytic (fun _ : Fin r => μ) q
      (fun jk : Fin n × Fin N => d jk.2 * c jk.1)
      (fun jk i s a => localTest (φ jk.2 i) a * f jk.1 i a * w i s a)
      R (fun jk i => hint jk.1 i (φ jk.2 i)) hR
    refine ⟨?_, ∑ jk, RatFunc.C (d jk.2 * c jk.1) * ∏ i, R jk i, ?_, ?_⟩
    · simpa only [he] using hi
    · simpa only [he] using hc
    · apply RationalContinuationLinear.linear_combination_mem_span
      intro jk _
      exact Set.mem_iUnion.mpr ⟨jk.1, R jk, (fun i => ⟨φ jk.2 i, hR jk i⟩), rfl⟩
  refine ⟨fun Φ => (hΦ Φ).1, fun Φ => ?_, ?_⟩
  · obtain ⟨R, hR, _⟩ := (hΦ Φ).2
    exact ⟨R, hR⟩
  · apply RationalContinuationLinear.commonDenominator_of_mem_span hV
    rintro R ⟨Φ, hR⟩
    obtain ⟨S, hS, hm⟩ := (hΦ Φ).2
    rwa [hR.unique hq hS]

theorem mellin_family_of_each {H P A : Type*} [MeasurableSpace A]
    (μ : Measure A) (q : ℕ) (X : Finset H) (I : H → P → ℂ → A → ℂ)
    (h : ∀ η ∈ X,
      (∀ Φ, ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I η Φ s) μ) ∧
      (∀ Φ, ∃ R, HasRationalContinuation q (fun s => ∫ a, I η Φ s a ∂μ) R) ∧
      HasCommonDenominator
        {R | ∃ Φ, HasRationalContinuation q (fun s => ∫ a, I η Φ s a ∂μ) R}) :
    (∀ η ∈ X, ∀ Φ, ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I η Φ s) μ) ∧
    (∀ η ∈ X, ∀ Φ, ∃ R, HasRationalContinuation q (fun s => ∫ a, I η Φ s a ∂μ) R) ∧
    HasCommonDenominator
      {R | ∃ η ∈ X, ∃ Φ, HasRationalContinuation q (fun s => ∫ a, I η Φ s a ∂μ) R} := by
  classical
  refine ⟨fun η hη => (h η hη).1, fun η hη => (h η hη).2.1, ?_⟩
  have hd := commonDenominator_iUnion
    (fun η : X => {R | ∃ Φ, HasRationalContinuation q (fun s => ∫ a, I η Φ s a ∂μ) R})
    (fun η => (h η η.property).2.2)
  apply commonDenominator_subset hd
  rintro R ⟨η, hη, Φ, hΦ⟩
  exact Set.mem_iUnion.mpr ⟨⟨η, hη⟩, Φ, hΦ⟩

open HarmonicAnalysis in
theorem finiteFunctionMellin_of_inputs
    (htensor : FiniteFunctionTensorStatement.{u})
    (hscalar : OneVariableMellinStatement.{u}) :
    FiniteFunctionMellinStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := T.fieldT2
  let := field_totallyDisconnected F T
  let := localHaar_sigmaFinite F T
  dsimp only
  intro r m hm X hX
  apply mellin_family_of_each (Measure.pi (fun _ : Fin r => localMultiplicativeHaar F.Carrier))
    T.residueCardinality X
  intro η hη
  obtain ⟨n, c, f, hf, he⟩ := htensor F.Carrierˣ r η (hX η hη)
  have hs (j : Fin n) (i : Fin r) :=
    hscalar p hp F T (m i) (hm i) (f j i) (hf j i).1 (hf j i).2
  apply mellin_of_expansions (localMultiplicativeHaar F.Carrier)
    T.residueCardinality T.residueCardinality_gt_one r n η c f he
    (fun Φ : SchwartzBruhat (Fin r → F.Carrier) => fun a => Φ (fun i => (a i : F.Carrier)))
    (fun φ : SchwartzBruhat F.Carrier => fun a => φ (a : F.Carrier))
    ?_ (fun i s a => (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m i : ℂ) * s))
    (fun j i => (hs j i).1) (fun j i => (hs j i).2.1) (fun j i => (hs j i).2.2)
  intro Φ
  obtain ⟨N, d, φ, hφ⟩ := rowTensorDecomposition F.Carrier r Φ
  exact ⟨N, d, φ, fun a => hφ (fun i => (a i : F.Carrier))⟩

end MellinAssembly

universe uF

/-- Actual torus Mellin convergence, rational continuation, and a Laurent
denominator uniform over the finite family and all Schwartz--Bruhat tests. -/
theorem finiteFunctionMellin : FiniteFunctionMellinStatement.{uF} :=
  MellinAssembly.finiteFunctionMellin_of_inputs
    finiteFunctionTensor.{uF} oneVariableMellin.{uF}

end Langlands.RankinSelberg
