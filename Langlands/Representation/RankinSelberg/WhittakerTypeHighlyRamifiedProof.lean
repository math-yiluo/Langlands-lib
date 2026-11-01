import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.ModelAsymptoticProof
import Langlands.Representation.Whittaker.TypeAsymptoticProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.Whittaker.Twist
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.RankinSelberg.RootCoordinateProof
import Langlands.Representation.RankinSelberg.LaurentTransport
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.Representation.RankinSelberg.FiniteFunctionTensorProof
import Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof
import Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityProof
import Langlands.Representation.RankinSelberg.RootModelExpansionProof
import Langlands.Representation.RankinSelberg.NormalizedCompactIntegrationProof
import Langlands.Representation.RankinSelberg.RootSpectralWeightProof
import Langlands.Representation.RankinSelberg.QuotientRootIntegrationProof
import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
import Langlands.Representation.RankinSelberg.IntegrandContinuityProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowNormalizedCompactIntegrationProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityProof
import Langlands.LocalField.Topology
import Langlands.HarmonicAnalysis.RowTensorDecompositionProof
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Highly ramified L-vanishing for Whittaker-type pairs

The finite-function asymptotic argument gives one conductor bound before
every quasicharacter and test function. Laurentness forces the normalized
common denominator to be one, preserving its full measure certificate.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open _root_.Topology

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The actual principal-unit subgroups are open in the specified topology. -/
theorem isOpen_principalUnits (n : ℕ) :
    letI := T.topology
    IsOpen (T.principalUnits n : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hval : IsOpen {x : F.Carrier | T.discreteValuation x = 1} := by
    convert (Valuation.isOpen_sphere (v := ValuativeRel.valuation F.Carrier)
      one_ne_zero) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Valuation.restrict_eq_one_iff]
    change e (ValuativeRel.valuation F.Carrier x) = 1 ↔
      ValuativeRel.valuation F.Carrier x = 1
    constructor
    · intro h
      exact e.strictMono.injective (h.trans (map_one e).symm)
    · intro h
      rw [h, map_one]
  have hint : IsOpen (T.Integers : Set F.Carrier) := Valuation.isOpen_integer
  convert (hval.preimage Units.continuous_val).inter
    (hint.preimage ((Units.continuous_val.sub continuous_const).div_const
      (T.uniformizer ^ (n : ℤ)))) using 1
  ext u
  exact T.mem_principalUnits_iff_div_mem_integers n u

/-- A continuous quasicharacter of a p-adic field has open kernel. -/
theorem quasicharacter_isOpen_ker
    (χ : letI := T.topology; HarmonicAnalysis.Quasicharacter F.Carrier) :
    letI := T.topology
    IsOpen ((χ : F.Carrierˣ →* ℂˣ).ker : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨n, hn⟩ := T.exists_multiplicativeTrivialAt χ
  exact Subgroup.isOpen_mono (fun u hu => hn u hu) (T.isOpen_principalUnits n)

end Langlands.PadicField.TopologicalData

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial
open scoped BigOperators

universe uF uV uW

section TensorIntegrals

/-- The Laurent continuation relation is closed under finite products,
including the empty product. -/
theorem hasRationalContinuation_finset_prod {ι : Type*} {q : ℕ}
    (t : Finset ι) (f : ι → ℂ → ℂ) (L : ι → LaurentCoefficients)
    (h : ∀ i ∈ t, HasRationalContinuation q (f i) (laurentToRatFunc (L i))) :
    HasRationalContinuation q (fun s => ∏ i ∈ t, f i s)
      (laurentToRatFunc (∏ i ∈ t, L i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp [RatFunc.denom_one]⟩
  | @insert i t hi ih =>
    simpa only [Finset.prod_insert hi, map_mul] using
      (h i (Finset.mem_insert_self i t)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Products of scalar integrands with right-half-plane integrability and
Laurent continuation have both properties for the actual product measure. -/
theorem laurentContinuation_product_integral
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)] {q : ℕ}
    (f : ι → ℂ → E → ℂ)
    (h : ∀ i,
      (∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (f i s) (μ i)) ∧
      ∃ L : LaurentCoefficients,
        HasRationalContinuation q (fun s => ∫ a, f i s a ∂μ i)
          (laurentToRatFunc L)) :
    (∃ c : ℝ, ∀ s : ℂ, c < s.re →
      Integrable (fun a : ι → E => ∏ i, f i s (a i)) (Measure.pi μ)) ∧
    ∃ L : LaurentCoefficients,
      HasRationalContinuation q
        (fun s => ∫ a : ι → E, ∏ i, f i s (a i) ∂Measure.pi μ)
        (laurentToRatFunc L) := by
  classical
  choose c hc using fun i => (h i).1
  choose L hL using fun i => (h i).2
  obtain ⟨b, hb⟩ := (Set.finite_range c).bddAbove
  refine ⟨⟨b, fun s hs => Integrable.fintype_prod
    (fun i => hc i s ((hb (Set.mem_range_self i)).trans_lt hs))⟩, ?_⟩
  refine ⟨∏ i, L i, ?_⟩
  simpa only [integral_fintype_prod_eq_prod] using
    hasRationalContinuation_finset_prod Finset.univ
      (fun i s => ∫ a, f i s a ∂μ i) L (fun i _ => hL i)

/-- Finite linear combinations of actual scalar integrals preserve convergence
and Laurent continuation on a common right half-plane. -/
theorem laurentContinuation_sum_integral
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) {q : ℕ} (c : ι → ℂ) (f : ι → ℂ → E → ℂ)
    (h : ∀ i,
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (f i s) μ) ∧
      ∃ L : LaurentCoefficients,
        HasRationalContinuation q (fun s => ∫ a, f i s a ∂μ)
          (laurentToRatFunc L)) :
    (∃ b : ℝ, ∀ s : ℂ, b < s.re →
      Integrable (fun a => ∑ i, c i * f i s a) μ) ∧
    ∃ L : LaurentCoefficients,
      HasRationalContinuation q
        (fun s => ∫ a, ∑ i, c i * f i s a ∂μ)
        (laurentToRatFunc L) := by
  classical
  choose b hb using fun i => (h i).1
  choose L hL using fun i => (h i).2
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  have hInt : ∀ s : ℂ, B < s.re → ∀ i, Integrable (f i s) μ :=
    fun s hs i => hb i s ((hB (Set.mem_range_self i)).trans_lt hs)
  refine ⟨⟨B, fun s hs => integrable_finsetSum _ (fun i _ =>
    (hInt s hs i).const_mul (c i))⟩, ?_⟩
  refine ⟨∑ i, LaurentPolynomial.C (c i) * L i, ?_⟩
  apply RationalContinuationLinear.continuation_of_eq_on_right
    (f := fun s => ∑ i, c i * ∫ a, f i s a ∂μ)
  · simpa only [map_sum, map_mul, laurentToRatFunc_C] using
      RationalContinuationLinear.continuation_linear_combination
        Finset.univ c (fun i s => ∫ a, f i s a ∂μ)
        (fun i => laurentToRatFunc (L i)) (fun i _ => hL i)
  · refine ⟨B, fun s hs => ?_⟩
    rw [integral_finsetSum _ (fun i _ => (hInt s hs i).const_mul (c i))]
    simp only [integral_const_mul]

/-- Tensor expansions of both factors reduce an actual product-measure
integral to finite linear combinations of scalar products. -/
theorem laurentContinuation_tensor_integral
    {ι J K E : Type*} [Fintype ι] [Fintype J] [Fintype K]
    [MeasurableSpace E] (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)]
    {q : ℕ} (cη : J → ℂ) (cΦ : K → ℂ)
    (η : J → ι → E → ℂ) (φ : K → ι → E → ℂ)
    (ζ : ι → ℂ → E → ℂ)
    (h : ∀ k j i,
      (∃ b : ℝ, ∀ s : ℂ, b < s.re →
        Integrable (fun a => φ k i a * η j i a * ζ i s a) (μ i)) ∧
      ∃ L : LaurentCoefficients,
        HasRationalContinuation q
          (fun s => ∫ a, φ k i a * η j i a * ζ i s a ∂μ i)
          (laurentToRatFunc L)) :
    let f := fun (s : ℂ) (a : ι → E) =>
      (∑ k, cΦ k * ∏ i, φ k i (a i)) *
      (∑ j, cη j * ∏ i, η j i (a i)) * ∏ i, ζ i s (a i)
    (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (f s) (Measure.pi μ)) ∧
    ∃ L : LaurentCoefficients,
      HasRationalContinuation q (fun s => ∫ a, f s a ∂Measure.pi μ)
        (laurentToRatFunc L) := by
  classical
  have hprod := fun k j => laurentContinuation_product_integral μ
    (fun i s a => φ k i a * η j i a * ζ i s a) (h k j)
  have hsum := fun k => laurentContinuation_sum_integral (Measure.pi μ) cη
    (fun j s a => ∏ i, φ k i (a i) * η j i (a i) * ζ i s (a i))
    (hprod k)
  have htotal := laurentContinuation_sum_integral (Measure.pi μ) cΦ
    (fun k s a => ∑ j, cη j *
      ∏ i, φ k i (a i) * η j i (a i) * ζ i s (a i)) hsum
  have heq (s : ℂ) (a : ι → E) :
      (∑ k, cΦ k * ∏ i, φ k i (a i)) *
        (∑ j, cη j * ∏ i, η j i (a i)) * ∏ i, ζ i s (a i) =
      ∑ k, cΦ k * ∑ j, cη j *
        ∏ i, φ k i (a i) * η j i (a i) * ζ i s (a i) := by
    simp only [Finset.prod_mul_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [heq] using htotal

end TensorIntegrals

/-- Scalar ramified Mellin certificates and the published positive-power
conductor theorem give one threshold for a fixed finite tensor family. -/
theorem exists_uniform_ramified_tensor_integrals
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    let dμ := localMultiplicativeHaar F.Carrier
    let scalar := fun (η : F.Carrierˣ → ℂ) (α : Quasicharacter F.Carrier)
        (m : ℕ) (φ : SchwartzBruhat F.Carrier) (s : ℂ) (a : F.Carrierˣ) =>
      φ (a : F.Carrier) * η a * (α a : ℂ) *
        (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s)
    ∀ {J : Type*} [Fintype J] (r : ℕ) (m : Fin r → ℕ),
      (∀ i, 0 < m i) →
      ∀ (η : J → Fin r → F.Carrierˣ → ℂ) (cη : J → ℂ),
      (∀ j i, ∃ b : ℕ, ∀ α : Quasicharacter F.Carrier,
        (∃ u ∈ T.principalUnits b, α u ≠ 1) →
        ∀ φ : SchwartzBruhat F.Carrier,
          (∃ c : ℝ, ∀ s : ℂ, c < s.re →
            Integrable (scalar (η j i) α (m i) φ s) dμ) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, scalar (η j i) α (m i) φ s a ∂dμ)
              (laurentToRatFunc L)) →
      ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
        A ≤ T.multiplicativeConductor χ →
        ∀ (K : ℕ) (cΦ : Fin K → ℂ)
          (φ : Fin K → Fin r → SchwartzBruhat F.Carrier),
        let f := fun (s : ℂ) (a : Fin r → F.Carrierˣ) =>
          (∑ k, cΦ k * ∏ i, φ k i (a i : F.Carrier)) *
          (∑ j, cη j * ∏ i, η j i (a i)) *
          ∏ i, (χ (a i) : ℂ) ^ (m i) *
            (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s)
        (∃ c : ℝ, ∀ s : ℂ, c < s.re →
          Integrable (f s) (Measure.pi fun _ : Fin r => dμ)) ∧
        ∃ L : LaurentCoefficients,
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, f s a ∂Measure.pi fun _ : Fin r => dμ)
            (laurentToRatFunc L) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : SecondCountableTopology F.Carrierˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  dsimp only
  intro J _ r m hm η cη hscalar
  choose b hb using hscalar
  choose B hB using fun j i =>
    (principalUnitPowerCofinality p F T (b j i) (m i) (hm i)).2
  obtain ⟨A, hA⟩ :=
    (Set.finite_range (fun ji : J × Fin r => B ji.1 ji.2)).bddAbove
  refine ⟨A, fun χ hχ K cΦ φ => ?_⟩
  apply laurentContinuation_tensor_integral
    (fun _ : Fin r => localMultiplicativeHaar F.Carrier)
    cη cΦ η (fun k i a => φ k i (a : F.Carrier))
    (fun i s a => (χ a : ℂ) ^ (m i) *
      (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m i : ℂ) * s))
  intro k j i
  obtain ⟨u, hu, hne⟩ := hB j i χ
    ((hA (Set.mem_range_self (j, i))).trans hχ)
  have hnontrivial : ∃ u ∈ T.principalUnits (b j i), (χ ^ m i) u ≠ 1 :=
    ⟨u, hu, by simpa only [ContinuousMonoidHom.pow_apply] using hne⟩
  simpa only [ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val, mul_assoc]
    using hb j i (χ ^ m i) hnontrivial (φ k i)

/-- The published finite-function tensor, scalar ramified Mellin and power
theorems give a threshold for a fixed finite torus family and every test
admitting a Schwartz tensor expansion. -/
theorem exists_uniform_ramified_finiteFamily_integrals
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    let dμ := localMultiplicativeHaar F.Carrier
    ∀ (r : ℕ) (m : Fin r → ℕ), (∀ i, 0 < m i) →
    (∀ Φ : SchwartzBruhat (Fin r → F.Carrier),
      ∃ (K : ℕ) (c : Fin K → ℂ)
        (φ : Fin K → Fin r → SchwartzBruhat F.Carrier),
        ∀ x, Φ x = ∑ k, c k * ∏ i, φ k i (x i)) →
    ∀ {ι : Type*} [Fintype ι] (η : ι → (Fin r → F.Carrierˣ) → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fin r → F.Carrierˣ =>
            fun a : Fin r → F.Carrierˣ => η j (b * a)))) →
    ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
      A ≤ T.multiplicativeConductor χ →
      ∀ j (Φ : SchwartzBruhat (Fin r → F.Carrier)),
        let f := fun (s : ℂ) (a : Fin r → F.Carrierˣ) =>
          Φ (fun i => (a i : F.Carrier)) * η j a *
            ∏ i, (χ (a i) : ℂ) ^ (m i) *
              (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s)
        (∃ c : ℝ, ∀ s : ℂ, c < s.re →
          Integrable (f s) (Measure.pi fun _ : Fin r => dμ)) ∧
        ∃ L : LaurentCoefficients,
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, f s a ∂Measure.pi fun _ : Fin r => dμ)
            (laurentToRatFunc L) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  dsimp only
  intro r m hm hSchwartz ι _ η hη
  have heach (j : ι) :
      ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
        A ≤ T.multiplicativeConductor χ →
        ∀ Φ : SchwartzBruhat (Fin r → F.Carrier),
          let f := fun (s : ℂ) (a : Fin r → F.Carrierˣ) =>
            Φ (fun i => (a i : F.Carrier)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (m i) *
                (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s)
          (∃ c : ℝ, ∀ s : ℂ, c < s.re →
            Integrable (f s)
              (Measure.pi fun _ : Fin r => localMultiplicativeHaar F.Carrier)) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, f s a
                ∂Measure.pi fun _ : Fin r => localMultiplicativeHaar F.Carrier)
              (laurentToRatFunc L) := by
    obtain ⟨N, cη, fη, hfη, hηexp⟩ :=
      finiteFunctionTensor F.Carrierˣ r (η j) (hη j)
    have hsc := fun k i =>
      ramifiedFiniteFunctionMellin p inferInstance F T (fη k i) (hfη k i)
    choose b hb using hsc
    obtain ⟨A, hA⟩ := exists_uniform_ramified_tensor_integrals T r m hm fη cη
      (fun k i => ⟨b k i, fun α hα φ => hb k i α hα (m i) (hm i) φ⟩)
    refine ⟨A, fun χ hχ Φ => ?_⟩
    obtain ⟨K, cΦ, φ, hΦ⟩ := hSchwartz Φ
    simpa only [hΦ, hηexp] using hA χ hχ K cΦ φ
  choose B hB using heach
  obtain ⟨A, hA⟩ := (Set.finite_range B).bddAbove
  exact ⟨A, fun χ hχ j Φ =>
    hB j χ ((hA (Set.mem_range_self j)).trans hχ) Φ⟩

/-- The published scalar, power and tensor theorems give the root-weight
torus certificates used by both rank adapters, with one threshold before
every quasicharacter and test. -/
theorem exists_uniform_ramified_root_integrals
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    let dμ := localMultiplicativeHaar F.Carrier
    ∀ n : ℕ,
    ∀ (N : ℕ) (η : Fin N → (Fin (n + 1) → F.Carrierˣ) → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fin (n + 1) → F.Carrierˣ =>
            fun a : Fin (n + 1) → F.Carrierˣ => η j (b * a)))) →
    ∃ B : ℕ, ∀ χ : Quasicharacter F.Carrier,
      B ≤ T.multiplicativeConductor χ →
      ∀ j (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        let f := fun (s : ℂ) (a : Fin (n + 1) → F.Carrierˣ) =>
          Φ (fun i => (a i : F.Carrier)) * η j a *
            ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
              (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
        (∃ c : ℝ, ∀ s : ℂ, c < s.re →
          Integrable (f s) (Measure.pi fun _ : Fin (n + 1) => dμ)) ∧
        ∃ L : LaurentCoefficients,
          HasRationalContinuation T.residueCardinality
            (fun s => ∫ a, f s a ∂Measure.pi fun _ : Fin (n + 1) => dμ)
            (laurentToRatFunc L) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  dsimp only
  intro n N η hη
  simpa only [Nat.cast_add, Nat.cast_one] using
    exists_uniform_ramified_finiteFamily_integrals T
      (n + 1) (fun i => i.val + 1) (fun _ => Nat.succ_pos _)
      (rowTensorDecomposition F.Carrier (n + 1)) η hη

/-- The Laurent divisibility interface forces a normalized generator to be one
when every generating rational value is a Laurent polynomial. -/
theorem normalizedGenerator_eq_one_of_laurent
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P)
    (hL : ∀ R ∈ values, ∃ L : LaurentCoefficients, laurentToRatFunc L = R) :
    P = 1 := by
  have hsub : zetaSpan values ≤
      Submodule.span LaurentCoefficients {(1 : RationalFunctions)} := by
    apply Submodule.span_le.mpr
    intro R hR
    obtain ⟨L, rfl⟩ := hL R hR
    apply Submodule.mem_span_singleton.mpr
    exact ⟨L, by simp [Algebra.smul_def, algebraMap_laurent]⟩
  have hrec : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈
      Submodule.span LaurentCoefficients {(1 : RationalFunctions)} := by
    apply hsub
    rw [hP.2]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hdvd : P ∣ 1 := (normalizedReciprocalLaurentSpanDivisibility P 1 hP.1 one_ne_zero).mp (by simpa using hrec)
  have hdeg : P.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp
    (isUnit_iff_dvd_one.mpr hdvd)
  rw [Polynomial.eq_C_of_degree_eq_zero hdeg, hP.1, map_one]

section PadicWhittakerType

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Existing symmetric factor existence supplies an ordered certificate for
any continuous determinant twist when the first rank is at least the second. -/
theorem exists_isPadicPairLPolynomial_quasicharacter_twist
    (hex : SymmetricLPolynomialExistenceStatement.{uF, uV, uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hnr : n ≤ r)
    (hπ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) σ)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    ∃ P : ℂ[X], IsPadicPairLPolynomial F ψ ν.val
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ P := by
  obtain ⟨P, hP⟩ := hex p F ψ ν r n V W
    (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ
    ((isOfWhittakerType_quasicharacter_twist_iff F.canonicalTopologicalData ψ χ π).mpr hπ) hσ
  exact ⟨P, (isPadicSymmetricLPolynomial_of_le hnr).mp hP⟩

/-- Root coordinates give precisely the positive powers of the twisting
character, including powers divisible by the residue characteristic. -/
theorem determinantCharacter_rootCoordinates (T : F.TopologicalData)
    (χ : F.Carrierˣ →* ℂˣ) (a : Fin (n + 1) → F.Carrierˣ)
    (k : Langlands.GeneralLinear (n + 1) F.Carrier) :
    (χ.comp determinant)
      (Iwasawa.diagonalUnits (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * k) =
        (∏ i : Fin (n + 1), χ (a i) ^ (i.val + 1)) * χ (determinant k) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hdet : determinant
      (Iwasawa.diagonalUnits (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j)) =
      ∏ i : Fin (n + 1), a i ^ (i.val + 1) := by
    apply Units.ext
    change Matrix.det (Iwasawa.diagonalUnits
      (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j)).val = _
    simpa only [Units.coe_prod, Units.val_pow_eq_pow_val] using
      (((rootCoordinateChange F T n).2.2.2.2.2.2 a).2.2.1)
  change χ (determinant (_ * k)) = _
  rw [map_mul, hdet, map_mul, map_prod]
  simp only [map_pow]

end PadicWhittakerType

/-- The untwisted coefficient expansions fix the finite family before every
determinant twist. The character of the right translate is absorbed in the
Schwartz coefficients; the exact positive coordinate powers remain explicit. -/
theorem exists_equalRankRootExpansion_twist
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (n : ℕ) :
    letI := T.topology
    let A := Fin (n + 1) → F.Carrierˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      CoefficientTorusExpansion (standardCharacter ψ n) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : F.Carrierˣ →* ℂˣ)
        (f : WhittakerFunctions ψ n),
        f ∈ whittakerSet ψ n (Langlands.twist (χ.comp determinant) π) →
      ∀ (f' : InverseWhittakerFunctions ψ n),
        f' ∈ inverseWhittakerSet ψ n σ →
      ∀ (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
        (k : Langlands.GeneralLinear (n + 1) F.Carrier),
      ∃ Ψ : Fin N → SchwartzBruhat (Fin (n + 1) → F.Carrier),
        ∀ a : A,
          let g := Iwasawa.diagonalUnits (d a) * k
          f.val g * f'.val g * Φ (lastRow g) * w a =
            ∑ j, Ψ j (fun i => (a i : F.Carrier)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) := by
  classical
  let := T.topology
  dsimp only
  intro V _ _ W _ _ π σ ψ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ := equalRankRootExpansion F T n V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ f hf f' hf' Φ k
  obtain ⟨f₀, ⟨ℓ₀, hf₀⟩, htw⟩ := (mem_whittakerSet_twist_iff ψ χ).mp hf
  obtain ⟨ℓ', hf'⟩ := hf'
  obtain ⟨Ψ, hΨ⟩ := hexp ℓ₀ ℓ' ⟨f₀, hf₀⟩ ⟨f', hf'⟩ Φ k
  refine ⟨fun j => (χ (determinant k) : ℂ) • Ψ j, ?_⟩
  intro a
  have hχ :
      (χ (determinant
        (Iwasawa.diagonalUnits
          (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * k)) : ℂ) =
      (∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) * (χ (determinant k) : ℂ) := by
    simpa only [MonoidHom.comp_apply, Units.val_mul, Units.coe_prod,
      Units.val_pow_eq_pow_val] using
      congrArg Units.val (determinantCharacter_rootCoordinates T χ a k)
  rw [htw, hχ]
  calc
    _ = ((∑ j, Ψ j (fun i => (a i : F.Carrier)) * η j a) *
        (χ (determinant k) : ℂ)) *
          ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) := by
      rw [← hΨ a]
      ring
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      change (Ψ j (fun i => (a i : F.Carrier)) * η j a *
          (χ (determinant k) : ℂ)) *
            (∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) =
        ((χ (determinant k) : ℂ) * Ψ j (fun i => (a i : F.Carrier))) *
          η j a * (∏ i, (χ (a i) : ℂ) ^ (i.val + 1))
      ring

/-- The actual normalized compact average for every determinant twist uses
the same finite family fixed by the untwisted coefficient expansions. -/
theorem exists_equalRankCompactRootExpansion_twist
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
    let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
    let A := Fin (n + 1) → F.Carrierˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ n) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : Quasicharacter F.Carrier)
        (ℓ : glFunctionals ψ n
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π))
        (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      ∃ (r : ℕ) (c : Fin r → ℝ)
        (Ψ : Fin r → Fin N → SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        (∀ t, 0 ≤ c t) ∧ (∑ t, c t) = 1 ∧
        ∀ (a : A) (s : ℂ),
          let H := fun z : Langlands.GeneralLinear (n + 1) F.Carrier =>
            equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
              (Iwasawa.diagonalUnits (d a) * z) * w a
          let S := fun t : Fin r =>
            ∑ j, Ψ t j (fun i => (a i : F.Carrier)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
                (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
                  ((i.val + 1 : ℂ) * s)
          Integrable H κ ∧
          (∫ z, H z ∂κ) = ∑ t, (c t : ℂ) * S t ∧
          (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let v : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  dsimp only
  intro V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_equalRankRootExpansion_twist T n V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ ℓ ℓ' f f' Φ
  have hsχ : IsSmooth
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (T.quasicharacter_isOpen_ker χ))).mpr hsπ
  obtain ⟨r, k, c, hc, hmass, havg⟩ :=
    equalRankNormalizedCompactIntegration F T n V W _ σ hsχ hsσ ψ ℓ ℓ' f f' Φ
  choose Ψ hΨ using fun t : Fin r =>
    hexp χ f.val ⟨ℓ, f.property⟩ f'.val ⟨ℓ', f'.property⟩ Φ (k t).val
  refine ⟨r, c, Ψ, hc, hmass, ?_⟩
  intro a s
  let H₀ := fun z : Langlands.GeneralLinear (n + 1) F.Carrier =>
    equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
      (Iwasawa.diagonalUnits (d a) * z)
  let S := fun t : Fin r =>
    ∑ j, Ψ t j (fun i => (a i : F.Carrier)) * η j a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  have hpoint (t : Fin r) : H₀ (k t).val * w a = S t := by
    have hdet := ((rootSpectralWeight F T n).2 a (k t).val
      ((rootSpectralWeight F T n).1 (k t)) s).1
    change (f.val.val _ * f'.val.val _ * Φ (lastRow _) *
      determinantWeight (normalizedAbsoluteValue T) _ s) * w a = S t
    rw [hdet]
    change (f.val.val _ * f'.val.val _ * Φ (lastRow _) * v a s) * w a = S t
    calc
      _ = (f.val.val _ * f'.val.val _ * Φ (lastRow _) * w a) * v a s := by ring
      _ = (∑ j, Ψ t j (fun i => (a i : F.Carrier)) * η j a *
          ∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) * v a s :=
        congrArg (fun z : ℂ => z * v a s) (hΨ t a)
      _ = S t := by
        simp only [Finset.sum_mul, Finset.prod_mul_distrib, S, v, mul_assoc]
  obtain ⟨hi, hsum, habs⟩ := havg (Iwasawa.diagonalUnits (d a)) s
  change Integrable (fun z => H₀ z * w a) κ ∧
    (∫ z, H₀ z * w a ∂κ) = ∑ t, (c t : ℂ) * S t ∧
    (∫⁻ z, ‖H₀ z * w a‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ
  refine ⟨hi.mul_const (w a), ?_, ?_⟩
  · rw [integral_mul_const, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, hpoint]
  · calc
      (∫⁻ z, ‖H₀ z * w a‖ₑ ∂κ) = (∫⁻ z, ‖H₀ z‖ₑ ∂κ) * ‖w a‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_mul_const' _ _ enorm_ne_top
      _ = (∑ t, ENNReal.ofReal (c t) * ‖H₀ (k t).val‖ₑ) * ‖w a‖ₑ := by rw [habs]
      _ = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_assoc, ← enorm_mul, hpoint]

/-- Uniform Laurent certificates for fixed finite torus families transfer to
every actual equal-rank zeta value, at every compatible quotient measure.
The torus and Iwasawa inputs remain explicit analytic hypotheses. -/
theorem exists_equalRank_ramified_laurent
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (n : ℕ) (hI : QuotientIwasawaIntegrationStatement F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    let A := Fin (n + 1) → F.Carrierˣ
    let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
    let I := fun (χ : Quasicharacter F.Carrier) (η : A → ℂ)
        (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) (a : A) =>
      Ψ (fun i => (a i : F.Carrier)) * η a *
        ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
          (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
    (∀ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) →
      ∃ B : ℕ, ∀ χ : Quasicharacter F.Carrier,
        B ≤ T.multiplicativeConductor χ →
        ∀ j (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
          (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I χ (η j) Ψ s) dA) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, I χ (η j) Ψ s a ∂dA) (laurentToRatFunc L)) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ n) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ B : ℕ, ∀ χ : Quasicharacter F.Carrier,
      B ≤ T.multiplicativeConductor χ →
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ R ∈ equalRankZetaValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ
            (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ,
          ∃ L : LaurentCoefficients, laurentToRatFunc L = R := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let I := fun (χ : Quasicharacter F.Carrier) (η : A → ℂ)
      (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) (a : A) =>
    Ψ (fun i => (a i : F.Carrier)) * η a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  dsimp only
  intro htorus V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_equalRankCompactRootExpansion_twist T n V W π σ ψ hsπ hsσ hπ hσ
  obtain ⟨B, hB⟩ := htorus N η hη
  refine ⟨B, fun χ hχ hright μ hμ R hR => ?_⟩
  rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, Φ, _hconv, hR⟩
  let fm : (coefficientModel
    (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule := ⟨f, hf⟩
  let fm' : (coefficientModel σ ℓ').toSubmodule := ⟨f', hf'⟩
  obtain ⟨r, c, Ψ, _hc, _hmass, hformula⟩ := hexp χ ℓ ℓ' fm fm' Φ
  let H := fun (s : ℂ) (a : A) (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
    equalRankFunction ψ (normalizedAbsoluteValue T) f f' Φ s
      (Iwasawa.diagonalUnits (d a) * z) * w a
  let S := fun (t : Fin r) (s : ℂ) (a : A) => ∑ j, I χ (η j) (Ψ t j) s a
  have hsum (s : ℂ) (a : A) :
      (∫ z, H s a z ∂κ) = ∑ t, (c t : ℂ) * S t s a :=
    (hformula a s).2.1
  have habs (s : ℂ) (a : A) :
      (∫⁻ z, ‖H s a z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t s a‖ₑ :=
    (hformula a s).2.2
  have hSdata (t : Fin r) :
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (S t s) dA) ∧
      ∃ L : LaurentCoefficients,
        HasRationalContinuation T.residueCardinality
          (fun s => ∫ a, S t s a ∂dA) (laurentToRatFunc L) := by
    simpa only [one_mul] using
      laurentContinuation_sum_integral dA (fun _ : Fin N => (1 : ℂ))
        (fun j => I χ (η j) (Ψ t j)) (fun j => hB χ hχ j (Ψ t j))
  have htotal := laurentContinuation_sum_integral dA
    (fun t => (c t : ℂ)) S hSdata
  choose b hb using fun t => (hSdata t).1
  obtain ⟨b₀, hb₀⟩ := (Set.finite_range b).bddAbove
  have hS (s : ℂ) (hs : b₀ < s.re) (t : Fin r) : Integrable (S t s) dA :=
    hb t s ((hb₀ (Set.mem_range_self t)).trans_lt hs)
  have hnorm (s : ℂ) (hs : b₀ < s.re) :
      (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤ := by
    simp_rw [habs]
    rw [lintegral_finsetSum' Finset.univ
      (f := fun t a => ENNReal.ofReal (c t) * ‖S t s a‖ₑ)
      (fun t _ => aemeasurable_const.mul (hS s hs t).aestronglyMeasurable.enorm)]
    apply ENNReal.sum_lt_top.mpr
    intro t _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp (hS s hs t).hasFiniteIntegral)
  have hsχ : IsSmooth
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (T.quasicharacter_isOpen_ker χ))).mpr hsπ
  have hmeas (s : ℂ) :
      Measurable (equalRankIntegrand ψ (normalizedAbsoluteValue T) f f' Φ s) :=
    (equalRankIntegrandContinuous F.Carrier n (normalizedAbsoluteValue T)
      (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
      V W _ σ hsχ hsσ ψ ℓ ℓ' fm fm' Φ s).measurable
  have htransport (s : ℂ) :
      (EqualRankConverges ψ (normalizedAbsoluteValue T) μ f f' Φ s ↔
        (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      (EqualRankConverges ψ (normalizedAbsoluteValue T) μ f f' Φ s →
        equalRankIntegral ψ (normalizedAbsoluteValue T) μ f f' Φ s =
          ∫ a, ∫ z, H s a z ∂κ ∂dA) :=
    (quotientRootIntegration F T n hI μ hμ).2
      (equalRankIntegrand ψ (normalizedAbsoluteValue T) f f' Φ s) (hmeas s)
  obtain ⟨L, hL⟩ := htotal.2
  have hLactual : HasRationalContinuation T.residueCardinality
      (equalRankIntegral ψ (normalizedAbsoluteValue T) μ f f' Φ) (laurentToRatFunc L) := by
    apply RationalContinuationLinear.continuation_of_eq_on_right hL
    refine ⟨b₀, fun s hs => ?_⟩
    rw [(htransport s).2 ((htransport s).1.mpr (hnorm s hs))]
    simp_rw [hsum]
  exact ⟨L, hLactual.unique T.residueCardinality_gt_one hR⟩

/-- The published zero-row root expansion fixes the same finite family before
every twist. The larger block has precisely the smaller determinant. -/
theorem exists_unequalRankZeroRowRootExpansion_twist
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    let A := Fin (n + 1) → F.Carrierˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ
        (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : F.Carrierˣ →* ℂˣ)
        (f : WhittakerFunctions ψ (n + (0 + k + 1))),
        f ∈ whittakerSet ψ (n + (0 + k + 1))
          (Langlands.twist (χ.comp determinant) π) →
      ∀ (f' : InverseWhittakerFunctions ψ n),
        f' ∈ inverseWhittakerSet ψ n σ →
      ∀ z : K,
      ∃ Ψ : Fin N → SchwartzBruhat (Fin (n + 1) → F.Carrier),
        ∀ (a : A) (s : ℂ),
          unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f f' s 0
              (Iwasawa.diagonalUnits (d a) * z.val) * w a =
            ∑ j, Ψ j (fun i => (a i : F.Carrier)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
                (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
                  ((i.val + 1 : ℂ) * s) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  dsimp only
  intro V _ _ W _ _ π σ ψ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    unequalRankZeroRowRootExpansion F T n k V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ f hf f' hf' z
  obtain ⟨f₀, ⟨ℓ₀, hf₀⟩, htw⟩ := (mem_whittakerSet_twist_iff ψ χ).mp hf
  obtain ⟨ℓ', hf'⟩ := hf'
  obtain ⟨Ψ, hΨ⟩ := hexp ℓ₀ ℓ' ⟨f₀, hf₀⟩ ⟨f', hf'⟩ z
  refine ⟨fun j => (χ (determinant z.val) : ℂ) • Ψ j, ?_⟩
  intro a s
  have hχ :
      (χ (determinant
        (Iwasawa.diagonalUnits
          (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * z.val)) : ℂ) =
      (∏ i, (χ (a i) : ℂ) ^ (i.val + 1)) * (χ (determinant z.val) : ℂ) := by
    simpa only [MonoidHom.comp_apply, Units.val_mul, Units.coe_prod,
      Units.val_pow_eq_pow_val] using
      congrArg Units.val (determinantCharacter_rootCoordinates T χ a z.val)
  have htwfun (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
      unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f f' s 0 g =
        (χ (determinant g) : ℂ) *
          unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f₀ f' s 0 g := by
    simp only [unequalRankFunction, htw, determinant_unequalRankMatrix]
    ring
  rw [htwfun, hχ]
  calc
    _ = (χ (determinant z.val) : ℂ) *
        (unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f₀ f' s 0
          (Iwasawa.diagonalUnits
            (fun i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j) * z.val) *
            (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
              ((i.val + 1) * (n - i.val)))⁻¹) *
          ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) := by ring
    _ = _ := by
      rw [hΨ a s]
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib]
      apply Finset.sum_congr rfl
      intro j _
      change _ = ((χ (determinant z.val) : ℂ) *
        Ψ j (fun i => (a i : F.Carrier))) * η j a * _
      ring

/-- The published zero-row compact integration theorem gives exact ordinary
and absolute averages for twists, with the untwisted root family unchanged. -/
theorem exists_unequalRankZeroRowCompactRootExpansion_twist
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
    let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
    let A := Fin (n + 1) → F.Carrierˣ
    let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    let w : A → ℂ := fun a =>
      (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
        ((i.val + 1) * (n - i.val)))⁻¹
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ
        (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
      ∀ (χ : Quasicharacter F.Carrier)
        (ℓ : glFunctionals ψ (n + (0 + k + 1))
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π))
        (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ (r : ℕ) (c : Fin r → ℝ)
        (Ψ : Fin r → Fin N → SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        (∀ t, 0 ≤ c t) ∧ (∑ t, c t) = 1 ∧
        ∀ (a : A) (s : ℂ),
          let H := fun z : Langlands.GeneralLinear (n + 1) F.Carrier =>
            unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
              (Iwasawa.diagonalUnits (d a) * z) * w a
          let S := fun t : Fin r =>
            ∑ j, Ψ t j (fun i => (a i : F.Carrier)) * η j a *
              ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
                (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
                  ((i.val + 1 : ℂ) * s)
          Integrable H κ ∧
          (∫ z, H z ∂κ) = ∑ t, (c t : ℂ) * S t ∧
          (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  dsimp only
  intro V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_unequalRankZeroRowRootExpansion_twist T n k V W π σ ψ hπ hσ
  refine ⟨N, η, hη, ?_⟩
  intro χ ℓ ℓ' f f'
  have hsχ : IsSmooth
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (T.quasicharacter_isOpen_ker χ))).mpr hsπ
  obtain ⟨r, z, c, hc, hmass, havg⟩ :=
    unequalRankZeroRowNormalizedCompactIntegration F T n k V W _ σ hsχ hsσ ψ ℓ ℓ' f f'
  choose Ψ hΨ using fun t : Fin r =>
    hexp χ f.val ⟨ℓ, f.property⟩ f'.val ⟨ℓ', f'.property⟩ (z t)
  refine ⟨r, c, Ψ, hc, hmass, ?_⟩
  intro a s
  let H₀ := fun u : Langlands.GeneralLinear (n + 1) F.Carrier =>
    unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
      (Iwasawa.diagonalUnits (d a) * u)
  let S := fun t : Fin r =>
    ∑ j, Ψ t j (fun i => (a i : F.Carrier)) * η j a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  have hpoint (t : Fin r) : H₀ (z t).val * w a = S t := hΨ t a s
  obtain ⟨hi, hsum, habs⟩ := havg (Iwasawa.diagonalUnits (d a)) s
  change Integrable (fun u => H₀ u * w a) κ ∧
    (∫ u, H₀ u * w a ∂κ) = ∑ t, (c t : ℂ) * S t ∧
    (∫⁻ u, ‖H₀ u * w a‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ
  refine ⟨hi.mul_const (w a), ?_, ?_⟩
  · rw [integral_mul_const, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, hpoint]
  · calc
      (∫⁻ u, ‖H₀ u * w a‖ₑ ∂κ) = (∫⁻ u, ‖H₀ u‖ₑ ∂κ) * ‖w a‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_mul_const' _ _ enorm_ne_top
      _ = (∑ t, ENNReal.ofReal (c t) * ‖H₀ (z t).val‖ₑ) * ‖w a‖ₑ := by rw [habs]
      _ = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_assoc, ← enorm_mul, hpoint]

/-- Uniform Laurent certificates for fixed finite torus families transfer to
every actual zero-row unequal-rank zeta value, at every compatible quotient measure.
The torus and Iwasawa inputs remain explicit analytic hypotheses. -/
theorem exists_unequalRankZeroRow_ramified_laurent
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (n k : ℕ) (hI : QuotientIwasawaIntegrationStatement F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    let A := Fin (n + 1) → F.Carrierˣ
    let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
    let I := fun (χ : Quasicharacter F.Carrier) (η : A → ℂ)
        (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) (a : A) =>
      Ψ (fun i => (a i : F.Carrier)) * η a *
        ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
          (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
    (∀ (N : ℕ) (η : Fin N → A → ℂ),
      (∀ j, Continuous (η j) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η j (b * a)))) →
      ∃ B : ℕ, ∀ χ : Quasicharacter F.Carrier,
        B ≤ T.multiplicativeConductor χ →
        ∀ j (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
          (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I χ (η j) Ψ s) dA) ∧
          ∃ L : LaurentCoefficients,
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ a, I χ (η j) Ψ s a ∂dA) (laurentToRatFunc L)) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ
        (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      IsSmooth π → IsSmooth σ →
      CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ B : ℕ, ∀ χ : Quasicharacter F.Carrier,
      B ≤ T.multiplicativeConductor χ →
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ (ν : AdditiveHaarMeasure F.Carrier),
        ∀ R ∈ unequalRankZetaValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) 0 k μ (rectangularMeasure ν 0 (n + 1))
            (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ,
          ∃ L : LaurentCoefficients, laurentToRatFunc L = R := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let I := fun (χ : Quasicharacter F.Carrier) (η : A → ℂ)
      (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) (a : A) =>
    Ψ (fun i => (a i : F.Carrier)) * η a *
      ∏ i, (χ (a i) : ℂ) ^ (i.val + 1) *
        (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  dsimp only
  intro htorus V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨N, η, hη, hexp⟩ :=
    exists_unequalRankZeroRowCompactRootExpansion_twist T n k
      V W π σ ψ hsπ hsσ hπ hσ
  obtain ⟨B, hB⟩ := htorus N η hη
  refine ⟨B, fun χ hχ hright μ hμ ν R hR => ?_⟩
  rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, _hconv, hR⟩
  let fm : (coefficientModel
    (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule := ⟨f, hf⟩
  let fm' : (coefficientModel σ ℓ').toSubmodule := ⟨f', hf'⟩
  obtain ⟨r, c, Ψ, _hc, _hmass, hformula⟩ := hexp χ ℓ ℓ' fm fm'
  let H := fun (s : ℂ) (a : A) (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
    unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f f' s 0
      (Iwasawa.diagonalUnits (d a) * z) * w a
  let S := fun (t : Fin r) (s : ℂ) (a : A) => ∑ j, I χ (η j) (Ψ t j) s a
  have hsum (s : ℂ) (a : A) :
      (∫ z, H s a z ∂κ) = ∑ t, (c t : ℂ) * S t s a :=
    (hformula a s).2.1
  have habs (s : ℂ) (a : A) :
      (∫⁻ z, ‖H s a z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t s a‖ₑ :=
    (hformula a s).2.2
  have hSdata (t : Fin r) :
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (S t s) dA) ∧
      ∃ L : LaurentCoefficients,
        HasRationalContinuation T.residueCardinality
          (fun s => ∫ a, S t s a ∂dA) (laurentToRatFunc L) := by
    simpa only [one_mul] using
      laurentContinuation_sum_integral dA (fun _ : Fin N => (1 : ℂ))
        (fun j => I χ (η j) (Ψ t j)) (fun j => hB χ hχ j (Ψ t j))
  have htotal := laurentContinuation_sum_integral dA
    (fun t => (c t : ℂ)) S hSdata
  choose b hb using fun t => (hSdata t).1
  obtain ⟨b₀, hb₀⟩ := (Set.finite_range b).bddAbove
  have hS (s : ℂ) (hs : b₀ < s.re) (t : Fin r) : Integrable (S t s) dA :=
    hb t s ((hb₀ (Set.mem_range_self t)).trans_lt hs)
  have hnorm (s : ℂ) (hs : b₀ < s.re) :
      (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤ := by
    simp_rw [habs]
    rw [lintegral_finsetSum' Finset.univ
      (f := fun t a => ENNReal.ofReal (c t) * ‖S t s a‖ₑ)
      (fun t _ => aemeasurable_const.mul (hS s hs t).aestronglyMeasurable.enorm)]
    apply ENNReal.sum_lt_top.mpr
    intro t _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp (hS s hs t).hasFiniteIntegral)
  have hsχ : IsSmooth
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) :=
    (Langlands.isSmooth_twist_iff _ π
      (determinantCharacter_openKernel _ (T.quasicharacter_isOpen_ker χ))).mpr hsπ
  have hmeas (s : ℂ) :
      Measurable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) :=
    (unequalRankZeroRowIntegrandContinuous F.Carrier n k (normalizedAbsoluteValue T)
      (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
      V W _ σ hsχ hsσ ψ ℓ ℓ' fm fm' s).measurable
  have htransport (s : ℂ) :
      (Integrable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) μ ↔
        (∫⁻ a, ∫⁻ z, ‖H s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      (Integrable (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) μ →
        (∫ q, unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0 q ∂μ) =
          ∫ a, ∫ z, H s a z ∂κ ∂dA) :=
    (quotientRootIntegration F T n hI μ hμ).2
      (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f f' s 0) (hmeas s)
  obtain ⟨L, hL⟩ := htotal.2
  have hLactual : HasRationalContinuation T.residueCardinality
      (unequalRankIntegral ψ (normalizedAbsoluteValue T) 0 k μ
        (rectangularMeasure ν 0 (n + 1)) f f') (laurentToRatFunc L) := by
    apply RationalContinuationLinear.continuation_of_eq_on_right hL
    refine ⟨b₀, fun s hs => ?_⟩
    simp only [unequalRankIntegral, rectangularMeasure_zero_rows, integral_dirac]
    rw [(htransport s).2 ((htransport s).1.mpr (hnorm s hs))]
    simp_rw [hsum]
  exact ⟨L, hLactual.unique T.residueCardinality_gt_one hR⟩

section Pair

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {r n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {P : ℂ[X]}

/-- A determinant twist may be moved from the larger member to the smaller
member without changing the certified pair polynomial. -/
theorem isPairLPolynomial_twist_left_iff_right (χ : Fˣ →* ℂˣ) :
    IsPairLPolynomial q ψ abv μ ν (Langlands.twist (χ.comp determinant) π) σ P ↔
      IsPairLPolynomial q ψ abv μ ν π (Langlands.twist (χ.comp determinant) σ) P := by
  have h := isPairLPolynomial_twist (π := π)
    (σ := Langlands.twist (χ.comp determinant) σ)
    (q := q) (ψ := ψ) (abv := abv) (μ := μ) (ν := ν) (P := P) χ
  simpa only [show (χ⁻¹).comp (determinant (n := n + 1)) =
    (χ.comp determinant)⁻¹ from rfl, Langlands.twist_inv_twist] using h

/-- In unequal rank, Laurentness of all values in the zero-row block forces
an already common pair polynomial to be one. -/
theorem IsPairLPolynomial.eq_one_of_laurent_zeroBlock
    (hnr : n < r) (hP : IsPairLPolynomial q ψ abv μ ν π σ P)
    (hL : ∀ R ∈ unequalRankZetaValuesAt 0 (r - n - 1) (by omega)
      q ψ abv μ (rectangularMeasure ν 0 (n + 1)) π σ,
      ∃ L : LaurentCoefficients, laurentToRatFunc L = R) : P = 1 := by
  have hgen := (isPairLPolynomial_of_lt hnr).mp hP 0 (r - n - 1) (by omega)
  exact normalizedGenerator_eq_one_of_laurent hgen hL

/-- In equal rank, Laurentness of the whole zeta-value family forces an
already certified pair polynomial to be one. -/
theorem IsPairLPolynomial.eq_one_of_laurent_equalRank
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (hP : IsPairLPolynomial q ψ abv μ ν π σ P)
    (hL : ∀ R ∈ equalRankZetaValues q ψ abv μ π σ,
      ∃ L : LaurentCoefficients, laurentToRatFunc L = R) : P = 1 := by
  exact normalizedGenerator_eq_one_of_laurent
    (isPairLPolynomial_self.mp hP) hL

end Pair

section PadicTwist

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {P : ℂ[X]}

/-- Laurentness for one compatible measure and the zero-row block determines
the common polynomial, without discarding any other measure or block. -/
theorem IsPadicPairLPolynomial.eq_one_of_laurent_zeroBlock
    (hnr : n < r) (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hL :
      letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := borel F.Carrier
      letI : BorelSpace F.Carrier := ⟨rfl⟩
      letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
      letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (upperUnipotent (n + 1) F.Carrier)
      letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      ∃ _ : Measure.IsMulRightInvariant (unipotentHaar F.Carrier n),
        ∃ μ : Measure (LeftUnipotentQuotient n F.Carrier),
          QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F.Carrier)
            (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ ∧
          ∀ R ∈ unequalRankZetaValuesAt 0 (r - n - 1) (by omega)
              F.canonicalTopologicalData.residueCardinality ψ
              (normalizedAbsoluteValue F.canonicalTopologicalData) μ
              (rectangularMeasure ν 0 (n + 1)) π σ,
            ∃ L : LaurentCoefficients, laurentToRatFunc L = R) : P = 1 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  obtain ⟨h, μ, hμ, hL⟩ := hL
  let := h
  exact (hP.2 μ hμ).eq_one_of_laurent_zeroBlock hnr hL

/-- The equal-rank family at one compatible measure likewise determines
the polynomial in the full p-adic pair certificate. -/
theorem IsPadicPairLPolynomial.eq_one_of_laurent_equalRank
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hL :
      letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := borel F.Carrier
      letI : BorelSpace F.Carrier := ⟨rfl⟩
      letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
      letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (upperUnipotent (n + 1) F.Carrier)
      letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      ∃ _ : Measure.IsMulRightInvariant (unipotentHaar F.Carrier n),
        ∃ μ : Measure (LeftUnipotentQuotient n F.Carrier),
          QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F.Carrier)
            (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ ∧
          ∀ R ∈ equalRankZetaValues F.canonicalTopologicalData.residueCardinality ψ
              (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ,
            ∃ L : LaurentCoefficients, laurentToRatFunc L = R) : P = 1 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  obtain ⟨h, μ, hμ, hL⟩ := hL
  let := h
  exact (hP.2 μ hμ).eq_one_of_laurent_equalRank hL

/-- Moving a determinant twist preserves the entire compatible-measure
certificate, including its existence clause. -/
theorem isPadicPairLPolynomial_twist_left_iff_right
    (χ : F.Carrierˣ →* ℂˣ) :
    IsPadicPairLPolynomial F ψ ν (Langlands.twist (χ.comp determinant) π) σ P ↔
      IsPadicPairLPolynomial F ψ ν π (Langlands.twist (χ.comp determinant) σ) P := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  exact imp_congr_right fun _ => isPairLPolynomial_twist_left_iff_right χ

/-- Larger-first vanishing in the two possible orientations suffices for
the symmetric relation, with the twist on the original first member. -/
theorem exists_highlyRamified_symmetric_of_ordered
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hlarge : n ≤ r → ∃ A : ℕ,
      ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
        IsPadicPairLPolynomial F ψ ν
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ 1)
    (hsmall : r < n → ∃ A : ℕ,
      ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
        IsPadicPairLPolynomial F ψ ν
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) σ) π 1) :
    ∃ A : ℕ,
      ∀ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ 1 := by
  by_cases hnr : n ≤ r
  · obtain ⟨A, hA⟩ := hlarge hnr
    exact ⟨A, fun χ hχ => (isPadicSymmetricLPolynomial_of_le hnr).mpr (hA χ hχ)⟩
  · have hrn : r < n := Nat.lt_of_not_ge hnr
    obtain ⟨A, hA⟩ := hsmall hrn
    refine ⟨A, fun χ hχ => (isPadicSymmetricLPolynomial_of_lt hrn).mpr ?_⟩
    exact (isPadicPairLPolynomial_twist_left_iff_right
      (π := σ) (σ := π) (χ : F.Carrierˣ →* ℂˣ)).mp (hA χ hχ)

end PadicTwist

/-- Quotient Iwasawa integration, coefficient expansions and common factor
existence imply full ordered-pair vanishing, using the published scalar,
power and tensor proofs. The witness measure comes from the common certificate. -/
theorem exists_highlyRamified_ordered_pair_of_analytic_inputs
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (n : ℕ)
    (hI : QuotientIwasawaIntegrationStatement F F.canonicalTopologicalData n) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∀ (r : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      n ≤ r →
      IsOfWhittakerType r (standardCharacter ψ r) π →
      IsOfWhittakerType n (standardCharacter ψ n) σ →
      CoefficientTorusExpansion (standardCharacter ψ r) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
      (∀ χ : Quasicharacter F.Carrier, ∃ P : ℂ[X],
        IsPadicPairLPolynomial F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ P) →
    ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
      A ≤ T.multiplicativeConductor χ →
        IsPadicPairLPolynomial F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ 1 := by
  classical
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  dsimp only
  intro r V _ _ W _ _ π σ hnr hπ hσ heπ heσ hex
  have htorus := exists_uniform_ramified_root_integrals T n
  by_cases heq : r = n
  · subst r
    obtain ⟨A, hA⟩ := exists_equalRank_ramified_laurent T n hI htorus
      V W π σ ψ hπ.1.1 hσ.1.1 heπ heσ
    refine ⟨A, fun χ hχ => ?_⟩
    obtain ⟨P, hP⟩ := hex χ
    have hPone : P = 1 := hP.eq_one_of_laurent_equalRank (by
      obtain ⟨h, μ, hμ⟩ := hP.1
      let := h
      exact ⟨h, μ, hμ, hA χ hχ μ hμ⟩)
    exact hPone ▸ hP
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = n + (0 + k + 1) :=
      ⟨r - n - 1, by omega⟩
    obtain ⟨A, hA⟩ := exists_unequalRankZeroRow_ramified_laurent T n k hI
      htorus V W π σ ψ hπ.1.1 hσ.1.1 heπ heσ
    refine ⟨A, fun χ hχ => ?_⟩
    obtain ⟨P, hP⟩ := hex χ
    have hPone : P = 1 := by
      obtain ⟨h, μ, hμ⟩ := hP.1
      let := h
      have hgen := (isPairLPolynomial_of_lt (by omega : n < n + (0 + k + 1))).mp
        (hP.2 μ hμ) 0 k rfl
      exact normalizedGenerator_eq_one_of_laurent hgen (hA χ hχ μ hμ ν.val)
    exact hPone ▸ hP

/-- The analytic inputs in both orientations imply full symmetric vanishing.
Symmetric factor existence is used only in the original carrier universes;
in the smaller-first branch its twist is moved to the larger member. -/
theorem exists_highlyRamified_symmetric_of_analytic_inputs
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hex : SymmetricLPolynomialExistenceStatement.{uF,uV,uW})
    (hI : ∀ n, QuotientIwasawaIntegrationStatement F F.canonicalTopologicalData n) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∀ (r n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsOfWhittakerType r (standardCharacter ψ r) π →
      IsOfWhittakerType n (standardCharacter ψ n) σ →
      CoefficientTorusExpansion (standardCharacter ψ r) π →
      CoefficientTorusExpansion (inverseStandardCharacter ψ r) π →
      CoefficientTorusExpansion (standardCharacter ψ n) σ →
      CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
      A ≤ T.multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν.val
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ 1 := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  dsimp only
  intro r n V _ _ W _ _ π σ hπ hσ heπ heπInv heσ heσInv
  apply exists_highlyRamified_symmetric_of_ordered π σ
  · intro hnr
    refine exists_highlyRamified_ordered_pair_of_analytic_inputs ψ ν n
      (hI n) r π σ hnr
      hπ hσ heπ heσInv ?_
    intro χ
    exact exists_isPadicPairLPolynomial_quasicharacter_twist
      hex ψ ν π σ hnr hπ hσ χ
  · intro hrn
    refine exists_highlyRamified_ordered_pair_of_analytic_inputs ψ ν r
      (hI r) n σ π
      (Nat.le_of_lt hrn) hσ hπ heσ heπInv ?_
    intro χ
    obtain ⟨P, hP⟩ := hex p F ψ ν r n V W
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) σ
      ((isOfWhittakerType_quasicharacter_twist_iff T ψ χ π).mpr hπ) hσ
    refine ⟨P, ?_⟩
    exact (isPadicPairLPolynomial_twist_left_iff_right
      (π := σ) (σ := π) (χ : F.Carrierˣ →* ℂˣ)).mpr
        ((isPadicSymmetricLPolynomial_of_lt hrn).mp hP)

/-- Symmetric polynomial existence implies the exact target, using the
published full-torus expansion and normalized quotient Iwasawa integration.
The expansion proof is instantiated at the independent carrier universes. -/
theorem whittakerTypeHighlyRamifiedLVanishing_of_analytic_inputs
    (hex : SymmetricLPolynomialExistenceStatement.{uF,uV,uW}) :
    WhittakerTypeHighlyRamifiedLVanishingStatement.{uF,uV,uW} := by
  intro p hp F ψ ν r n V _ _ W _ _ π σ hπ hσ
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hπInv := (isOfWhittakerType_standard_iff_inverse ψ π).mp hπ
  have hσInv := (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  exact exists_highlyRamified_symmetric_of_analytic_inputs ψ ν hex
    (fun n => quotientIwasawaIntegration F T n) r n π σ hπ hσ
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uV}
      p hp F T r V π ψ _ (Or.inl rfl) hπ)
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uV}
      p hp F T r V π ψ _ (Or.inr rfl) hπInv)
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uW}
      p hp F T n W σ ψ _ (Or.inl rfl) hσ)
    (modelAsymptoticTransfer whittakerTypeAsymptotic.{uF,uW}
      p hp F T n W σ ψ _ (Or.inr rfl) hσInv)

/-- JPSS Proposition 2.13 for arbitrary Whittaker-type pairs: sufficiently
ramified determinant twists have symmetric L-polynomial one, with a uniform
natural conductor bound and the full compatible-measure certificate. -/
theorem whittakerTypeHighlyRamifiedLVanishing :
    WhittakerTypeHighlyRamifiedLVanishingStatement.{uF,uV,uW} :=
  whittakerTypeHighlyRamifiedLVanishing_of_analytic_inputs
    symmetricLPolynomialExists.{uF,uV,uW}

end Langlands.RankinSelberg
