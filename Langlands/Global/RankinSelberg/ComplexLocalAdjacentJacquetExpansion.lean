import Langlands.Global.RankinSelberg.ComplexLocalAdjacentIntegrals
import Langlands.Global.RankinSelberg.ComplexLocalEqualJacquetExpansion
import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZeroReduction

/-! # The complex adjacent-rank equation from the finite expansion in Jacquet §8.3 -/

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

/-- The smaller equal-rank and matrix equations imply the adjacent-rank equation for the
paired sums. The central scalar from the dual unfolding raises the sign power by one. -/
theorem pairMeromorphicEquation_adjacent_sum_products {r k : ℕ} (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (A Ad Z Zd : Fin k → ℂ → ℂ)
    (hA : ∀ i, PairMeromorphicEquation ds es a (complexCentralSign es ^ r) (A i) (Ad i))
    (hZ : ∀ i, PairMeromorphicEquation [d] es a 1 (Z i) (Zd i)) :
    PairMeromorphicEquation (d :: ds) es a (complexCentralSign es ^ (r + 1))
      (fun s => ∑ i, A i s * Z i s)
      (fun s => complexCentralSign es * ∑ i, Ad i s * Zd i s) := by
  unfold PairMeromorphicEquation at hA hZ ⊢
  filter_upwards [eventually_all.mpr hA, eventually_all.mpr hZ] with s hsA hsZ
  simp only [List.map_cons, complexPairLFactor, complexPairBlocks, List.flatMap_cons,
    complexLFactor_append, ReciprocalEntire.denominator_mul, mul_inv, mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  let L (xs ys : List ComplexCharacterData) := ((complexPairLFactor xs ys).denominator s)⁻¹
  let Ld (xs ys : List ComplexCharacterData) :=
    ((complexPairLFactor (xs.map ComplexCharacterData.inv)
      (ys.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹
  let L₁ := ((complexLFactor (es.map d.mul)).denominator s)⁻¹
  let L₁d := ((complexLFactor ((es.map ComplexCharacterData.inv).map d.inv.mul)).denominator (1 - s))⁻¹
  let E (xs ys : List ComplexCharacterData) :=
    (complexPairEpsilon xs ys a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
  change L₁ * (L ds es * (complexCentralSign es * (Ad i (1 - s) * Zd i (1 - s)))) =
    complexCentralSign es ^ (r + 1) *
      (E (d :: ds) es * (L₁d * (Ld ds es * (A i s * Z i s))))
  have ha : L ds es * Ad i (1 - s) =
      complexCentralSign es ^ r * E ds es * Ld ds es * A i s := hsA i
  have hz : L₁ * Zd i (1 - s) = E [d] es * L₁d * Z i s := by
    simpa only [L₁, L₁d, E, one_mul, complexPairLFactor, complexPairBlocks, List.map_cons,
      List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hsZ i
  have he : E (d :: ds) es = E [d] es * E ds es := by
    simp only [E, complexPairEpsilon, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, complexEpsilon_append, Units.val_mul]
  calc
    _ = complexCentralSign es * ((L ds es * Ad i (1 - s)) * (L₁ * Zd i (1 - s))) := by ring
    _ = _ := by rw [ha, hz, he, pow_succ]; ring

/-- Matched finite expansions of the two actual corank-one integrals on a right
half-plane, with meromorphic matrix factors for the removed first character. -/
def HasAdjacentJacquetExpansion {r : ℕ} (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ) : Prop :=
  ∃ (k : ℕ) (D₁ : Fin k → ComplexQuotientMeasureData r)
    (U₁ V₁ : Fin k → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ₁ : Fin k → SchwartzMap (Fin (r + 1) → ℂ) ℂ) (Z Zd : Fin k → ℂ → ℂ),
    (∀ i, U₁ i ∈ complexWhittakerModel r ds a ∧ V₁ i ∈ complexWhittakerModel r es (-a) ∧
      MeromorphicOn (Z i) Set.univ ∧ MeromorphicOn (Zd i) Set.univ ∧
      PairMeromorphicEquation [d] es a 1 (Z i) (Zd i)) ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      complexUnequalIntegral (Nat.lt_succ_self r) D W V s =
        ∑ i, complexEqualIntegral (D₁ i) (U₁ i) (V₁ i) (Φ₁ i) s * Z i s ∧
      complexUnequalDualIntegral (Nat.lt_succ_self r) a D W V s =
        complexCentralSign es *
          ∑ i, complexEqualDualIntegral a (D₁ i) (U₁ i) (V₁ i) (Φ₁ i) s * Zd i s

/-- Absolute convergence of both exact corank-one kernels on a right half-plane. -/
def HasAdjacentJacquetConvergence {r : ℕ} (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ) : Prop :=
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    Integrable (complexUnequalIntegrand (Nat.lt_succ_self r) W V s) D.measure ∧
    Integrable (complexUnequalDualKernel (Nat.lt_succ_self r) W V s)
      (complexUnequalDualMeasure (r := r + 1) a D)

/-- The analytic adjacent-rank package follows from the smaller equal-rank theorem,
absolute convergence and the matched finite expansion. -/
def ComplexLocalAdjacentJacquetExpansionReductionStatement : Prop :=
  ∀ (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    ds.length = r + 1 → es.length = r + 1 → ComplexLocalEqualAtRankStatement r →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
    HasAdjacentJacquetExpansion d ds es a D W V →
    HasAdjacentJacquetConvergence a D W V →
    UnequalEquation (Nat.lt_succ_self r) a D W V (d :: ds) es a (complexCentralSign es ^ (r + 1))

theorem complexLocalAdjacentJacquetExpansionReduction :
    ComplexLocalAdjacentJacquetExpansionReductionStatement := by
  intro r d ds es hd he hEqual a D W V hExpansion hConvergence
  obtain ⟨k, D₁, U₁, V₁, Φ₁, Z, Zd, hZ, τ, hτ⟩ := hExpansion
  obtain ⟨σ, hσ⟩ := hConvergence
  have hterms (i : Fin k) :
      ∃ (ρ : ℝ) (A Ad : ℂ → ℂ), MeromorphicOn A Set.univ ∧ MeromorphicOn Ad Set.univ ∧
        (∀ s : ℂ, ρ < s.re →
          complexEqualIntegral (D₁ i) (U₁ i) (V₁ i) (Φ₁ i) s = A s ∧
          complexEqualDualIntegral a (D₁ i) (U₁ i) (V₁ i) (Φ₁ i) s = Ad s) ∧
        PairMeromorphicEquation ds es a (complexCentralSign es ^ r) A Ad := by
    obtain ⟨ρ, A, Ad, _, _, _, _, hA, hAd, hEq, hEqd, hFE⟩ :=
      hEqual ds es hd he a (D₁ i) (U₁ i) (V₁ i) (Φ₁ i) (hZ i).1 (hZ i).2.1
    exact ⟨ρ, A, Ad, hA, hAd, fun s hs => ⟨hEq s hs, hEqd s hs⟩, hFE⟩
  choose ρ A Ad hA hAd hright hFE using hterms
  obtain ⟨β, hβ⟩ := (Set.finite_range ρ).bddAbove
  let b := max (max σ τ) β
  let M := fun s => ∑ i, A i s * Z i s
  let Md := fun s => complexCentralSign es * ∑ i, Ad i s * Zd i s
  have hmer : MeromorphicOn M Set.univ :=
    MeromorphicOn.fun_sum fun i _ => (hA i).mul (hZ i).2.2.1
  have hmerd : MeromorphicOn Md Set.univ := by
    change MeromorphicOn ((fun _ : ℂ => complexCentralSign es) *
      (fun s => ∑ i, Ad i s * Zd i s)) Set.univ
    exact (MeromorphicOn.const (complexCentralSign es)).mul
      (MeromorphicOn.fun_sum fun i _ => (hAd i).mul (hZ i).2.2.2.1)
  have hright_converges {s : ℂ} (hs : b < s.re) :=
    hσ s ((le_max_left σ τ).trans_lt ((le_max_left _ _).trans_lt hs))
  have hO : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨b, M, Md, fun _ hs => (hright_converges hs).1, fun _ hs => (hright_converges hs).2,
    differentiableOn_complexUnequalIntegral_of_integrable _ D W V hO
      (fun _ hs => (hright_converges hs).1),
    differentiableOn_complexUnequalDualIntegral_adjacent a D W V hO
      (fun _ hs => (hright_converges hs).2), hmer, hmerd, ?_, ?_, ?_⟩
  · intro s hs
    rw [(hτ s ((le_max_right σ τ).trans_lt ((le_max_left _ _).trans_lt hs))).1]
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hright i s ((hβ (Set.mem_range_self i)).trans_lt ((le_max_right _ _).trans_lt hs))).1]
  · intro s hs
    rw [(hτ s ((le_max_right σ τ).trans_lt ((le_max_left _ _).trans_lt hs))).2]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [(hright i s ((hβ (Set.mem_range_self i)).trans_lt ((le_max_right _ _).trans_lt hs))).2]
  · exact pairMeromorphicEquation_adjacent_sum_products d ds es a A Ad Z Zd hFE
      fun i => (hZ i).2.2.2.2

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
