import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.RankinSelberg.ComplexLocalEqualIntertwinerReduction
import Langlands.Global.RankinSelberg.ComplexUnequalJacquetConventionReduction

/-! # The equal-rank equation from the finite expansion in Jacquet §8.2 -/

noncomputable section

open Filter MeasureTheory
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The functional equation of a pair of continuations with the specified central sign. -/
def PairMeromorphicEquation (ds es : List ComplexCharacterData) (a : ℂˣ) (c : ℂ)
    (M Md : ℂ → ℂ) : Prop :=
  ∀ᶠ s in codiscrete ℂ,
    ((complexPairLFactor ds es).denominator s)⁻¹ * Md (1 - s) =
      c * (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
        ((complexPairLFactor (ds.map ComplexCharacterData.inv)
          (es.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * M s

private theorem complexPairLFactor_cons (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) :
    complexPairLFactor (d :: ds) es =
      (complexPairLFactor [d] es).mul (complexPairLFactor ds es) := by
  simpa only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using complexLFactor_append (es.map d.mul) (complexPairBlocks ds es)

private theorem complexPairEpsilon_cons (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    complexPairEpsilon (d :: ds) es a c hc s =
      complexPairEpsilon [d] es a c hc s * complexPairEpsilon ds es a c hc s := by
  simpa only [complexPairEpsilon, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using
    complexEpsilon_append (es.map d.mul) (complexPairBlocks ds es) a c hc s

private theorem equal_coefficient {r : ℕ} (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (hd : ds.length = r + 1) (he : es.length = r + 2)
    (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    complexCentralSign ds *
      ((complexCentralSign ds ^ (r + 1) * (complexPairEpsilon ds es (-a) c hc s : ℂ)) *
        (complexPairEpsilon [d] es a c hc s : ℂ)) =
      complexCentralSign es ^ (r + 1) * (complexPairEpsilon (d :: ds) es a c hc s : ℂ) := by
  rw [pair_epsilon_neg, hd, he, complexPairEpsilon_cons d ds es a c hc s, Units.val_mul]
  have hsq : (complexCentralSign ds ^ (r + 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, complexCentralSign_sq, one_pow]
  calc
    _ = (complexCentralSign ds ^ (r + 2)) ^ 2 *
          (complexCentralSign es ^ (r + 1) *
            ((complexPairEpsilon [d] es a c hc s : ℂ) *
              (complexPairEpsilon ds es a c hc s : ℂ))) := by
      rw [show r + 2 = (r + 1) + 1 from rfl, pow_succ (complexCentralSign ds) (r + 1)]
      ring
    _ = _ := by rw [hsq, one_mul]

/-- Multiply the corank-one and matrix equations in each term of the paired expansion.
The corank-one integrals put the original second representation first. -/
theorem pairMeromorphicEquation_equal_sum_products {r k : ℕ} (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (hd : ds.length = r + 1) (he : es.length = r + 2)
    (a : ℂˣ) (A Ad Z Zd : Fin k → ℂ → ℂ)
    (hA : ∀ i, PairMeromorphicEquation es ds (-a) (complexCentralSign ds ^ (r + 1))
      (A i) (Ad i))
    (hZ : ∀ i, PairMeromorphicEquation [d] es a 1 (Z i) (Zd i)) :
    PairMeromorphicEquation (d :: ds) es a (complexCentralSign es ^ (r + 1))
      (fun s => ∑ i, A i s * Z i s)
      (fun s => complexCentralSign ds * ∑ i, Ad i s * Zd i s) := by
  unfold PairMeromorphicEquation at hA hZ ⊢
  filter_upwards [eventually_all.mpr hA, eventually_all.mpr hZ] with s hsA hsZ
  simp only [List.map_cons, complexPairLFactor_cons d ds es,
    complexPairLFactor_cons d.inv (ds.map ComplexCharacterData.inv)
      (es.map ComplexCharacterData.inv), ReciprocalEntire.denominator_mul,
    mul_inv, mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha := hsA i
  rw [CuspidalPairPartialGammaGlobal.complexPairLFactor_denominator_comm es ds,
    CuspidalPairPartialGammaGlobal.complexPairLFactor_denominator_comm
      (es.map ComplexCharacterData.inv) (ds.map ComplexCharacterData.inv),
    CuspidalPairPartialGammaGlobal.complexPairEpsilon_comm es ds] at ha
  simp only [Units.val_neg, nnnorm_neg] at ha
  have hz := hsZ i
  simp only [one_mul] at hz
  let c := ‖(a : ℂ)‖₊
  have hc : 0 < c := nnnorm_pos.mpr a.ne_zero
  let L (xs ys : List ComplexCharacterData) := ((complexPairLFactor xs ys).denominator s)⁻¹
  let Ld (xs ys : List ComplexCharacterData) :=
    ((complexPairLFactor (xs.map ComplexCharacterData.inv)
      (ys.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹
  let E (xs ys : List ComplexCharacterData) (b : ℂˣ) :=
    (complexPairEpsilon xs ys b c hc s : ℂ)
  change L [d] es * (L ds es * (complexCentralSign ds * (Ad i (1 - s) * Zd i (1 - s)))) =
    complexCentralSign es ^ (r + 1) *
      (E (d :: ds) es a * (Ld [d] es * (Ld ds es * (A i s * Z i s))))
  change L ds es * Ad i (1 - s) =
    complexCentralSign ds ^ (r + 1) * E ds es (-a) * Ld ds es * A i s at ha
  change L [d] es * Zd i (1 - s) = E [d] es a * Ld [d] es * Z i s at hz
  calc
    _ = complexCentralSign ds * ((L ds es * Ad i (1 - s)) * (L [d] es * Zd i (1 - s))) := by ring
    _ = (complexCentralSign ds *
          ((complexCentralSign ds ^ (r + 1) * E ds es (-a)) * E [d] es a)) *
          (Ld [d] es * (Ld ds es * (A i s * Z i s))) := by rw [ha, hz]; ring
    _ = _ := by rw [equal_coefficient d ds es hd he a c hc s]; ring

/-- The specialization of the complex unequal-rank equation to `GL_(r+2) × GL_(r+1)`. -/
def ComplexLocalAdjacentAtRankStatement (r : ℕ) : Prop :=
  ∀ (es ds : List ComplexCharacterData), es.length = r + 2 → ds.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (V : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (U : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
    V ∈ complexWhittakerModel (r + 1) es a → U ∈ complexWhittakerModel r ds (-a) →
    UnequalEquation (Nat.lt_succ_self r) a D V U es ds a (complexCentralSign ds ^ (r + 1))

theorem complexLocalAdjacentAtRank_of_unequal (h : ComplexLocalUnequalFunctionalEquationStatement)
    (r : ℕ) : ComplexLocalAdjacentAtRankStatement r :=
  h (r + 1) r (Nat.lt_succ_self r)

/-- The two half-plane identities of Jacquet's expansion (8.2) with meromorphic
matrix continuations and the positive Fourier convention. The smaller-rank datum
may vary by summand, which permits concatenating finite expansions. -/
def HasEqualJacquetExpansion {r : ℕ} (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData (r + 1))
    (W V : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 2) → ℂ) ℂ) : Prop :=
  ∃ (k : ℕ) (D₁ : Fin k → ComplexQuotientMeasureData r)
    (U₁ : Fin k → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (V₁ : Fin k → Langlands.GeneralLinear (r + 2) ℂ → ℂ) (Z Zd : Fin k → ℂ → ℂ),
    (∀ i, U₁ i ∈ complexWhittakerModel r ds a ∧
      V₁ i ∈ complexWhittakerModel (r + 1) es (-a) ∧
      MeromorphicOn (Z i) Set.univ ∧ MeromorphicOn (Zd i) Set.univ ∧
      PairMeromorphicEquation [d] es a 1 (Z i) (Zd i)) ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      complexEqualIntegral D W V Φ s =
        ∑ i, complexUnequalIntegral (Nat.lt_succ_self r) (D₁ i) (V₁ i) (U₁ i) s * Z i s ∧
      complexEqualDualIntegral a D W V Φ s =
        complexCentralSign ds *
          ∑ i, complexUnequalDualIntegral (Nat.lt_succ_self r) (-a) (D₁ i) (V₁ i) (U₁ i) s * Zd i s

/-- The analytic conclusion of the local equal-rank equation follows from convergence,
the adjacent-rank functional equation, and a matched finite expansion. -/
def ComplexLocalEqualJacquetExpansionReductionStatement : Prop :=
  ∀ (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    ds.length = r + 1 → es.length = r + 2 → ComplexLocalAdjacentAtRankStatement r →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData (r + 1))
    (W V : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 2) → ℂ) ℂ),
    HasEqualJacquetExpansion d ds es a D W V Φ →
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand W V Φ s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 2) W)
        (ArchimedeanLocal.dualFunction (r + 2) V) (complexFourierTransform a Φ) s) D.measure) →
    ComplexLocalEqualPairStatement (d :: ds) es a D W V Φ

theorem complexLocalEqualJacquetExpansionReduction :
    ComplexLocalEqualJacquetExpansionReductionStatement := by
  intro r d ds es hd he hAdjacent a D W V Φ hExpansion hConvergence
  obtain ⟨k, D₁, U₁, V₁, Z, Zd, hZ, τ, hτ⟩ := hExpansion
  obtain ⟨σ, hσ⟩ := hConvergence
  have hterms (i : Fin k) :
      ∃ (ρ : ℝ) (A Ad : ℂ → ℂ), MeromorphicOn A Set.univ ∧ MeromorphicOn Ad Set.univ ∧
        (∀ s : ℂ, ρ < s.re →
          complexUnequalIntegral (Nat.lt_succ_self r) (D₁ i) (V₁ i) (U₁ i) s = A s ∧
          complexUnequalDualIntegral (Nat.lt_succ_self r) (-a) (D₁ i) (V₁ i) (U₁ i) s = Ad s) ∧
        PairMeromorphicEquation es ds (-a) (complexCentralSign ds ^ (r + 1)) A Ad := by
    obtain ⟨ρ, A, Ad, _, _, _, _, hA, hAd, hEq, hEqd, hFE⟩ :=
      hAdjacent es ds he hd (-a) (D₁ i) (V₁ i) (U₁ i) (hZ i).2.1
        (by simpa only [neg_neg] using (hZ i).1)
    exact ⟨ρ, A, Ad, hA, hAd, fun s hs => ⟨hEq s hs, hEqd s hs⟩, hFE⟩
  choose ρ A Ad hA hAd hright hFE using hterms
  obtain ⟨β, hβ⟩ := (Set.finite_range ρ).bddAbove
  let b := max (max σ τ) β
  let M := fun s => ∑ i, A i s * Z i s
  let Md := fun s => complexCentralSign ds * ∑ i, Ad i s * Zd i s
  have hmer : MeromorphicOn M Set.univ :=
    MeromorphicOn.fun_sum fun i _ => (hA i).mul (hZ i).2.2.1
  have hmerd : MeromorphicOn Md Set.univ := by
    change MeromorphicOn ((fun _ : ℂ => complexCentralSign ds) *
      (fun s => ∑ i, Ad i s * Zd i s)) Set.univ
    exact (MeromorphicOn.const (complexCentralSign ds)).mul
      (MeromorphicOn.fun_sum fun i _ => (hAd i).mul (hZ i).2.2.2.1)
  refine ⟨b, M, Md, ?_, ?_, hmer, hmerd, ?_, ?_, ?_⟩
  · intro s hs
    exact (hσ s ((le_max_left σ τ).trans_lt ((le_max_left _ _).trans_lt hs))).1
  · intro s hs
    exact (hσ s ((le_max_left σ τ).trans_lt ((le_max_left _ _).trans_lt hs))).2
  · intro s hs
    change complexEqualIntegral D W V Φ s = M s
    rw [(hτ s ((le_max_right σ τ).trans_lt ((le_max_left _ _).trans_lt hs))).1]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hright i s ((hβ (Set.mem_range_self i)).trans_lt ((le_max_right _ _).trans_lt hs))).1]
  · intro s hs
    change complexEqualDualIntegral a D W V Φ s = Md s
    rw [(hτ s ((le_max_right σ τ).trans_lt ((le_max_left _ _).trans_lt hs))).2]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hright i s ((hβ (Set.mem_range_self i)).trans_lt ((le_max_right _ _).trans_lt hs))).2]
  · exact pairMeromorphicEquation_equal_sum_products d ds es hd he a A Ad Z Zd hFE
      fun i => (hZ i).2.2.2.2

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
