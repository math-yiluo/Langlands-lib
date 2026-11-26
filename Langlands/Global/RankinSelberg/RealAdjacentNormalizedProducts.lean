import Langlands.Global.RankinSelberg.RealLocalNormalizedGrowth

/-! # Normalizing the real adjacent-rank finite product sums

See the paired Markdown file.
-/

noncomputable section

open scoped NNReal
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

/-- The pair `L`-factor of `x :: xs` against `ys` splits off the factor of `[x]`. -/
theorem realPairLFactor_cons (x : RealBlock) (xs ys : List RealBlock) :
    realPairLFactor (x :: xs) ys = (realPairLFactor [x] ys).mul (realPairLFactor xs ys) := by
  simpa only [realPairLFactor, realPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using realLFactor_append (ys.flatMap x.tensor) (realPairBlocks xs ys)

/-- The pair `ε`-factor of `x :: xs` against `ys` splits off the factor of `[x]`. -/
theorem realPairEpsilon_cons (x : RealBlock) (xs ys : List RealBlock) (b : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) (s : ℂ) :
    realPairEpsilon (x :: xs) ys b c hc s =
      realPairEpsilon [x] ys b c hc s * realPairEpsilon xs ys b c hc s := by
  simp only [realPairEpsilon, realPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, realEpsilon_append]

/-- Finite sums of products of two normalized pairs, for the lists `xs × es` and `[x] × es`,
form a normalized pair for `(x :: xs) × es`, after multiplying the two sums by scalars. The
scalars and signs are related by `κd · sA = sign · κ`. -/
def RealAdjacentNormalizedProductsStatement : Prop :=
  ∀ (m : ℕ) (x : RealBlock) (xs es : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c)
    (sA κ κd sign : ℂ) (A Ad Z Zd : Fin m → ℂ → ℂ),
    κd * sA = sign * κ →
    (∀ j, HasRealPairNormalizedGrowth xs es (xs.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) b c hc sA (A j) (Ad j)) →
    (∀ j, HasRealPairNormalizedGrowth [x] es ([x].map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) b c hc 1 (Z j) (Zd j)) →
    HasRealPairNormalizedGrowth (x :: xs) es ((x :: xs).map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) b c hc sign
      (fun s => κ * ∑ j, A j s * Z j s) (fun s => κd * ∑ j, Ad j s * Zd j s)

theorem realAdjacentNormalizedProducts : RealAdjacentNormalizedProductsStatement := by
  classical
  intro m x xs es b c hc sA κ κd sign A Ad Z Zd hsign hA hZ
  choose NA NdA hNA hNdA hNAg hNdAg hAR hAE using hA
  choose NZ NdZ hNZ hNdZ hNZg hNdZg hZR hZE using hZ
  choose τ hτ using hAR
  choose υ hυ using hZR
  obtain ⟨σ, hσ⟩ := (Set.finite_range fun j : Fin m => max (τ j) (υ j)).bddAbove
  refine ⟨fun s => κ * ∑ j, NA j s * NZ j s, fun s => κd * ∑ j, NdA j s * NdZ j s,
    ?_, ?_, ?_, ?_, ⟨σ, fun s hs => ?_⟩, fun s => ?_⟩
  · exact (differentiable_const κ).mul
      (Differentiable.fun_sum fun j _ => (hNA j).mul (hNZ j))
  · exact (differentiable_const κd).mul
      (Differentiable.fun_sum fun j _ => (hNdA j).mul (hNdZ j))
  · exact (HasStripExponentialGrowth.fun_sum Finset.univ (fun j s => NA j s * NZ j s)
      (fun j _ => (hNAg j).mul (hNZg j))).const_mul κ
  · exact (HasStripExponentialGrowth.fun_sum Finset.univ (fun j s => NdA j s * NdZ j s)
      (fun j _ => (hNdAg j).mul (hNdZg j))).const_mul κd
  · have hτs (j : Fin m) : τ j < s.re :=
      ((le_max_left (τ j) (υ j)).trans (hσ (Set.mem_range_self j))).trans_lt hs
    have hυs (j : Fin m) : υ j < s.re :=
      ((le_max_right (τ j) (υ j)).trans (hσ (Set.mem_range_self j))).trans_lt hs
    constructor
    · rw [realPairLFactor_cons, ReciprocalEntire.denominator_mul]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hτ j s (hτs j)).1, (hυ j s (hυs j)).1]
      ring
    · simp only [List.map_cons]
      rw [realPairLFactor_cons, ReciprocalEntire.denominator_mul]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hτ j s (hτs j)).2, (hυ j s (hυs j)).2]
      simp only [List.map_cons, List.map_nil]
      ring
  · simp only [Finset.mul_sum]
    have hε := realPairEpsilon_cons x xs es b c hc s
    calc
      _ = ∑ j, κd * ((sA * (realPairEpsilon xs es b c hc s : ℂ) * NA j s) *
          (1 * (realPairEpsilon [x] es b c hc s : ℂ) * NZ j s)) :=
        Finset.sum_congr rfl fun j _ => by rw [hAE j s, hZE j s]
      _ = ∑ j, (κd * sA) * (realPairEpsilon (x :: xs) es b c hc s : ℂ) *
          (NA j s * NZ j s) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hε, Units.val_mul]
        ring
      _ = _ := by
        rw [hsign]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

end Langlands.Global.RankinSelbergGlobal.RealJacquet
