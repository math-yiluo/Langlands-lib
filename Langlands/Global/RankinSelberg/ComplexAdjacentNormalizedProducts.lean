import Langlands.Global.RankinSelberg.ComplexUnequalJacquetConventionReduction
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Normalization and reflection of the adjacent-rank finite product sum -/

noncomputable section

open scoped NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ComplexJacquet (HasComplexPairNormalizedGrowth pair_epsilon_neg)

set_option autoImplicit false

/-- The specified entire functions normalize the raw integrals and satisfy the reflection. -/
def IsComplexPairNormalization (ds es : List ComplexCharacterData) (a : ℂˣ) (c : ℂ)
    (Z Zd N Nd : ℂ → ℂ) : Prop :=
  Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      N s = (complexPairLFactor ds es).denominator s * Z s ∧
      Nd s = (complexPairLFactor (ds.map ComplexCharacterData.inv)
        (es.map ComplexCharacterData.inv)).denominator s * Zd s) ∧
    ∀ s : ℂ, Nd (1 - s) = c *
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

/-- Two raw complex local integrals have entire normalizations realizing the given
functional equation and agreeing with the normalized raw integrals on a half-plane. -/
def HasComplexPairNormalization (ds es : List ComplexCharacterData) (a : ℂˣ) (c : ℂ)
    (Z Zd : ℂ → ℂ) : Prop :=
  ∃ N Nd : ℂ → ℂ, IsComplexPairNormalization ds es a c Z Zd N Nd

/-- Forget the extra strip growth once an entire functional equation is available. -/
theorem normalization_of_growth {ds es : List ComplexCharacterData} {a : ℂˣ} {c : ℂ} {Z Zd : ℂ → ℂ}
    (h : HasComplexPairNormalizedGrowth ds es a c Z Zd) : HasComplexPairNormalization ds es a c Z Zd := by
  obtain ⟨N, Nd, hN, hNd, _, _, hR, hEq⟩ := h
  exact ⟨N, Nd, hN, hNd, hR, hEq⟩

private theorem pairL_cons (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    complexPairLFactor (d :: ds) es =
      (complexPairLFactor [d] es).mul (complexPairLFactor ds es) := by
  simpa only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using complexLFactor_append (es.map d.mul) (complexPairBlocks ds es)

private theorem pairEpsilon_cons (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    complexPairEpsilon (d :: ds) es a c hc s =
      complexPairEpsilon [d] es a c hc s * complexPairEpsilon ds es a c hc s := by
  simpa only [complexPairEpsilon, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using
    complexEpsilon_append (es.map d.mul) (complexPairBlocks ds es) a c hc s

private theorem adjacentProduct_sign {r : ℕ} (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (hes : es.length = r + 1) (a : ℂˣ)
    (c : NNReal) (hc : 0 < c) (s : ℂ) :
    complexCentralSign es ^ r * (complexPairEpsilon ds es (-a) c hc s : ℂ) *
      (complexPairEpsilon [d] es a c hc s : ℂ) =
      (complexCentralSign es ^ (r + 1) *
        (complexPairEpsilon (d :: ds) es (-a) c hc s : ℂ)) *
        (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) := by
  have ha : (complexPairEpsilon [d] es a c hc s : ℂ) =
      ((d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * complexCentralSign es) *
        (complexPairEpsilon [d] es (-a) c hc s : ℂ) := by
    simpa only [neg_neg, hes, complexCentralSign, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, List.length_cons, List.length_nil, zero_add, pow_one, map_pow,
      Units.val_pow_eq_pow_val] using (pair_epsilon_neg [d] es (-a) c hc s)
  rw [ha, pairEpsilon_cons d ds es (-a) c hc s, Units.val_mul, pow_succ]
  ring

/-- The equal-rank and square normalizations of the compact summands combine
to the adjacent-rank normalization, with the ordinary adjoining sign. -/
def ComplexAdjacentNormalizedProductsStatement : Prop :=
  ∀ (r m : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    es.length = r + 1 →
  ∀ (a : ℂˣ) (A Ad Z Zd : Fin m → ℂ → ℂ),
    (∀ j, HasComplexPairNormalization ds es (-a) (complexCentralSign es ^ r) (A j) (Ad j)) →
    (∀ j, HasComplexPairNormalization [d] es a 1 (Z j) (Zd j)) →
    HasComplexPairNormalization (d :: ds) es (-a) (complexCentralSign es ^ (r + 1))
      (fun s => (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * ∑ j, A j s * Z j s)
      (fun s => ∑ j, Ad j s * Zd j s)

private theorem adjacentNormalizedProductWitnesses
    (r m : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (hes : es.length = r + 1) (a : ℂˣ) (A Ad Z Zd B Bd C Cd : Fin m → ℂ → ℂ)
    (hB : ∀ j, IsComplexPairNormalization ds es (-a) (complexCentralSign es ^ r) (A j) (Ad j) (B j) (Bd j))
    (hC : ∀ j, IsComplexPairNormalization [d] es a 1 (Z j) (Zd j) (C j) (Cd j)) :
    IsComplexPairNormalization (d :: ds) es (-a) (complexCentralSign es ^ (r + 1))
      (fun s => (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * ∑ j, A j s * Z j s)
      (fun s => ∑ j, Ad j s * Zd j s)
      (fun s => (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * ∑ j, B j s * C j s)
      (fun s => ∑ j, Bd j s * Cd j s) := by
  classical
  choose τ hτ using fun j => (hB j).2.2.1
  choose υ hυ using fun j => (hC j).2.2.1
  obtain ⟨σ, hσ⟩ := (Set.finite_range fun j : Fin m => max (τ j) (υ j)).bddAbove
  let ε := (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ)
  refine ⟨?_, ?_, ⟨σ, ?_⟩, ?_⟩
  · exact (differentiable_const ε : Differentiable ℂ (fun _ : ℂ => ε)).mul
      (Differentiable.fun_sum fun j _ => (hB j).1.mul (hC j).1)
  · exact Differentiable.fun_sum fun j _ => (hB j).2.1.mul (hC j).2.1
  · intro s hs
    have hτs (j : Fin m) := ((le_max_left (τ j) (υ j)).trans
      (hσ (Set.mem_range_self j))).trans_lt hs
    have hυs (j : Fin m) := ((le_max_right (τ j) (υ j)).trans
      (hσ (Set.mem_range_self j))).trans_lt hs
    constructor
    · rw [pairL_cons d ds es, ReciprocalEntire.denominator_mul]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hτ j s (hτs j)).1, (hυ j s (hυs j)).1]
      ring
    · simp only [List.map_cons]
      rw [pairL_cons d.inv (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv),
        ReciprocalEntire.denominator_mul]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hτ j s (hτs j)).2, (hυ j s (hυs j)).2]
      simp only [List.map_cons, List.map_nil]
      ring
  · intro s
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have he := (hB j).2.2.2 s
    have hz := (hC j).2.2.2 s
    simp only [one_mul, Units.val_neg, nnnorm_neg] at he hz ⊢
    rw [he, hz]
    have hsign := adjacentProduct_sign d ds es hes a ‖(a : ℂ)‖₊
      (nnnorm_pos.mpr a.ne_zero) s
    calc
      _ = (complexCentralSign es ^ r * (complexPairEpsilon ds es (-a) ‖(a : ℂ)‖₊
          (nnnorm_pos.mpr a.ne_zero) s : ℂ) * (complexPairEpsilon [d] es a ‖(a : ℂ)‖₊
          (nnnorm_pos.mpr a.ne_zero) s : ℂ)) * (B j s * C j s) := by ring
      _ = _ := by rw [hsign]; ring

theorem complexAdjacentNormalizedProducts : ComplexAdjacentNormalizedProductsStatement := by
  classical
  intro r m d ds es hes a A Ad Z Zd hA hZ
  choose B Bd hB using hA
  choose C Cd hC using hZ
  exact ⟨_, _, adjacentNormalizedProductWitnesses r m d ds es hes a A Ad Z Zd B Bd C Cd hB hC⟩

/-- The adjacent product normalization preserves the strip growth of both lower pairs. -/
def ComplexAdjacentNormalizedProductsGrowthStatement : Prop :=
  ∀ (r m : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    es.length = r + 1 →
  ∀ (a : ℂˣ) (A Ad Z Zd : Fin m → ℂ → ℂ),
    (∀ j, HasComplexPairNormalizedGrowth ds es (-a) (complexCentralSign es ^ r) (A j) (Ad j)) →
    (∀ j, HasComplexPairNormalizedGrowth [d] es a 1 (Z j) (Zd j)) →
    HasComplexPairNormalizedGrowth (d :: ds) es (-a) (complexCentralSign es ^ (r + 1))
      (fun s => (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * ∑ j, A j s * Z j s)
      (fun s => ∑ j, Ad j s * Zd j s)

theorem complexAdjacentNormalizedProductsGrowth : ComplexAdjacentNormalizedProductsGrowthStatement := by
  classical
  intro r m d ds es hes a A Ad Z Zd hA hZ
  choose B Bd hB using hA
  choose C Cd hC using hZ
  have hB' (j : Fin m) : IsComplexPairNormalization ds es (-a) (complexCentralSign es ^ r)
      (A j) (Ad j) (B j) (Bd j) :=
    ⟨(hB j).1, (hB j).2.1, (hB j).2.2.2.2⟩
  have hC' (j : Fin m) : IsComplexPairNormalization [d] es a 1 (Z j) (Zd j) (C j) (Cd j) :=
    ⟨(hC j).1, (hC j).2.1, (hC j).2.2.2.2⟩
  obtain ⟨hN, hNd, hR, hEq⟩ := adjacentNormalizedProductWitnesses r m d ds es hes a
    A Ad Z Zd B Bd C Cd hB' hC'
  refine ⟨_, _, hN, hNd, ?_, ?_, hR, hEq⟩
  · exact (HasStripExponentialGrowth.fun_sum Finset.univ (fun j s => B j s * C j s)
      (fun j _ => (hB j).2.2.1.mul (hC j).2.2.1)).const_mul _
  · exact HasStripExponentialGrowth.fun_sum Finset.univ (fun j s => Bd j s * Cd j s)
      (fun j _ => (hB j).2.2.2.1.mul (hC j).2.2.2.1)

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
