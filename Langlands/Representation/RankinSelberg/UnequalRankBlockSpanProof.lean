import Langlands.Representation.RankinSelberg.UnequalRankBlockSpanStatement
import Langlands.Representation.RankinSelberg.UnequalRankBlockMatrix
import Langlands.Representation.RankinSelberg.UnequalRankBlockIntegrationProof
import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportStatement
import Langlands.Representation.RankinSelberg.UnequalRankCompactSupportProof
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.HarmonicAnalysis.RowFourier
import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityStatement
import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityProof
import Langlands.Representation.RankinSelberg.UnequalRankSmearingProof
import Langlands.Representation.RankinSelberg.UnequalRankFourierSmearingProof
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! Equality of adjacent JPSS block spans using supplied-measure integration
and Fourier smearing in the original coefficient model. -/

noncomputable section

namespace Langlands.RankinSelberg.AdjacentBlockReduction

open MeasureTheory HarmonicAnalysis

section LastRowCoefficient

open Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Last-row integration is realized in the original coefficient model whenever
one compact rectangular set supports all block evaluations. -/
theorem exists_lastRow_integral_coefficient [T2Space F]
    [MeasurableSpace F] [BorelSpace F] (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (n j k : ℕ) [BorelSpace (Fin (n + 1) → F)]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F) V)
    (hπ : IsSmooth π)
    (ℓ : glFunctionals ψ (n + ((j + 1) + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F)) (hC : IsCompact C)
    (hs : ∀ g X, f.val.val (unequalRankMatrix (j + 1) k g X) ≠ 0 → X ∈ C) :
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      ∀ (g : Langlands.GeneralLinear (n + 1) F)
        (Y : Matrix (Fin j) (Fin (n + 1)) F),
      Integrable (fun x => f.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y x)))
        (rowMeasure ν (n + 1)) ∧
      f₀.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y 0)) =
        ∫ x, f.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y x))
          ∂rowMeasure ν (n + 1) := by
  let U : (Fin (n + 1) → F) →
      Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F :=
    fun x => rectangularUnipotent (j + 1) k (Fin.snoc 0 x)
  have hU : Continuous U := continuous_lastRowUnipotent n j k
  let B := fun p : Langlands.GeneralLinear (n + 1) F × Matrix (Fin j) (Fin (n + 1)) F =>
    unequalRankMatrix (j + 1) k p.1 (Fin.snoc p.2 0)
  have hc : HasCompactSupport (fun x p => f.val.val (B p * U x)) := by
    apply HasCompactSupport.intro (hC.image (continuous_apply (Fin.last j)))
    intro x hx
    funext p
    change f.val.val (B p * U x) = 0
    rw [show B p * U x = unequalRankMatrix (j + 1) k p.1 (Fin.snoc p.2 x) from
      (unequalRankMatrix_snoc j k p.1 p.2 x).symm]
    by_contra hn
    apply hx
    exact ⟨Fin.snoc p.2 x, hs _ _ hn,
      @Fin.snoc_last j (fun _ => Fin (n + 1) → F) x (fun a b => p.2 a b)⟩
  obtain ⟨f₀, hf₀⟩ := exists_coefficient_fiber_integral
    (rowMeasure ν (n + 1)) π hπ ℓ U hU B f hc
  refine ⟨f₀, ?_⟩
  intro g Y
  simpa only [B, U, ← unequalRankMatrix_snoc] using hf₀ (g, Y)

set_option backward.isDefEq.respectTransparency false in
/-- A small normalized cutoff makes the last row invisible to the input
coefficient wherever the cutoff is nonzero. -/
theorem exists_normalized_lastRow_cutoff [T2Space F] [LocallyCompactSpace F]
    [TotallyDisconnectedSpace F] [MeasurableSpace F] [BorelSpace F]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (n j k : ℕ)
    [BorelSpace (Fin (n + 1) → F)] [(rowMeasure ν (n + 1)).IsOpenPosMeasure]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F) V)
    (hπ : IsSmooth π)
    (ℓ : glFunctionals ψ (n + ((j + 1) + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule) :
    ∃ Φ : SchwartzBruhat (Fin (n + 1) → F),
      (∫ x, Φ x ∂rowMeasure ν (n + 1)) = 1 ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F)
        (Y : Matrix (Fin j) (Fin (n + 1)) F) (x : Fin (n + 1) → F),
        Φ x * f.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y x)) =
          Φ x * f.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y 0)) := by
  obtain ⟨Φ, hΦ, hfix⟩ := Smearing.exists_normalized_coefficient_cutoff
    (rowMeasure ν (n + 1)) π hπ ℓ
    (fun x : Fin (n + 1) → F => rectangularUnipotent (j + 1) k (Fin.snoc 0 x))
    (continuous_lastRowUnipotent n j k) 0 (by
      change rectangularUnipotent (j + 1) k (Fin.snoc 0 0) = 1
      have hz : (Fin.snoc (0 : Matrix (Fin j) (Fin (n + 1)) F) 0 :
          Matrix (Fin (j + 1)) (Fin (n + 1)) F) = 0 := by
        funext a b
        induction a using Fin.lastCases <;> simp [Fin.snoc]
      rw [hz]
      exact rectangularUnipotent_zero (j + 1) k) f
  refine ⟨Φ, hΦ, ?_⟩
  intro g Y x
  by_cases hx : Φ x = 0
  · simp only [hx, zero_mul]
  · rw [unequalRankMatrix_snoc, hfix x hx]

end LastRowCoefficient

section AdjacentIntegral

open Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] [MeasurableSpace F] [BorelSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Integrating out the last row produces the neighboring block integral of a
single coefficient in the original representation. -/
theorem exists_adjacent_block_integral_coefficient (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (n r j k : ℕ)
    [BorelSpace (Fin (n + 1) → F)]
    [BorelSpace (Matrix (Fin (j + 1)) (Fin (n + 1)) F)]
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ r π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F)) (hC : IsCompact C)
    (hs : ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C) :
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      ∀ g : Langlands.GeneralLinear (n + 1) F,
      (∫ X, f.val.val (blockMatrixAt (j + 1) k h₁ g X)
        ∂rectangularMeasure ν (j + 1) (n + 1)) =
      ∫ Y, f₀.val.val (blockMatrixAt j (k + 1) h₂ g Y)
        ∂rectangularMeasure ν j (n + 1) := by
  subst r
  obtain ⟨f₀, hf₀⟩ := exists_lastRow_integral_coefficient ν n j k ψ π hπ ℓ f C hC hs
  refine ⟨f₀, ?_⟩
  intro g
  have hi := blockCoefficient_integrable ν n (j + 1) k ψ π hπ ℓ f C hC hs g
  calc
    _ = ∫ Y, ∫ x, f.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y x))
        ∂rowMeasure ν (n + 1) ∂rectangularMeasure ν j (n + 1) :=
      rectangular_integral_lastRow ν j (n + 1) _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with Y
      rw [← (hf₀ g Y).2]
      exact congrArg f₀.val.val (blockMatrixAt_snoc_zero j k rfl h₂ g Y)

set_option backward.isDefEq.respectTransparency false in
/-- Realizing every row cutoff in the same model gives the reverse block
integral transfer. Uniform support is used only to justify Fubini. -/
theorem exists_reverse_adjacent_block_integral_coefficient
    [LocallyCompactSpace F] [TotallyDisconnectedSpace F]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (n r j k : ℕ)
    [BorelSpace (Fin (n + 1) → F)] [(rowMeasure ν (n + 1)).IsOpenPosMeasure]
    [BorelSpace (Matrix (Fin (j + 1)) (Fin (n + 1)) F)]
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ r π)
    (hs : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F), IsCompact C ∧
        ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C)
    (f : (coefficientModel π ℓ).toSubmodule)
    (hcutoff : ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ f₁ : (coefficientModel π ℓ).toSubmodule, ∀ g X,
        f₁.val.val (blockMatrixAt (j + 1) k h₁ g X) =
          Φ (X (Fin.last j)) * f.val.val (blockMatrixAt (j + 1) k h₁ g X)) :
    ∃ f₁ : (coefficientModel π ℓ).toSubmodule,
      ∀ g : Langlands.GeneralLinear (n + 1) F,
      (∫ X, f₁.val.val (blockMatrixAt (j + 1) k h₁ g X)
        ∂rectangularMeasure ν (j + 1) (n + 1)) =
      ∫ Y, f.val.val (blockMatrixAt j (k + 1) h₂ g Y)
        ∂rectangularMeasure ν j (n + 1) := by
  subst r
  obtain ⟨Φ, hΦ, hfix⟩ := exists_normalized_lastRow_cutoff ν n j k ψ π hπ ℓ f
  obtain ⟨f₁, hf₁⟩ := hcutoff Φ
  obtain ⟨C, hC, hs₁⟩ := hs f₁
  refine ⟨f₁, ?_⟩
  intro g
  have hi := blockCoefficient_integrable ν n (j + 1) k ψ π hπ ℓ f₁ C hC hs₁ g
  calc
    _ = ∫ Y, ∫ x, f₁.val.val (blockMatrixAt (j + 1) k rfl g (Fin.snoc Y x))
        ∂rowMeasure ν (n + 1) ∂rectangularMeasure ν j (n + 1) :=
      rectangular_integral_lastRow ν j (n + 1) _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with Y
      calc
        (∫ x, f₁.val.val (blockMatrixAt (j + 1) k rfl g (Fin.snoc Y x))
            ∂rowMeasure ν (n + 1)) =
            ∫ x, Φ x * f.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y 0))
              ∂rowMeasure ν (n + 1) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hf₁]
          simpa only [Fin.snoc_last, blockMatrixAt] using hfix g Y x
        _ = f.val.val (unequalRankMatrix (j + 1) k g (Fin.snoc Y 0)) := by
          rw [integral_mul_const, hΦ, one_mul]
        _ = f.val.val (blockMatrixAt j (k + 1) h₂ g Y) :=
          congrArg f.val.val (blockMatrixAt_snoc_zero j k rfl h₂ g Y)

/-- The last-row coefficient transfer preserves every scalar integral, without
assuming existence of a rational continuation or quotient convergence. -/
theorem exists_adjacent_integral_coefficient (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (n r j k : ℕ)
    [BorelSpace (Fin (n + 1) → F)]
    [BorelSpace (Matrix (Fin (j + 1)) (Fin (n + 1)) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ r π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F)) (hC : IsCompact C)
    (hs : ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C) :
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      ∀ (f' : InverseWhittakerFunctions ψ n) (s : ℂ),
      unequalRankIntegralAt (j + 1) k h₁ ψ abv μ
          (rectangularMeasure ν (j + 1) (n + 1)) f.val f' s =
        unequalRankIntegralAt j (k + 1) h₂ ψ abv μ
          (rectangularMeasure ν j (n + 1)) f₀.val f' s := by
  obtain ⟨f₀, hf₀⟩ := exists_adjacent_block_integral_coefficient ν n r j k h₁ h₂
    ψ π hπ ℓ f C hC hs
  refine ⟨f₀, ?_⟩
  intro f' s
  rw [unequalRankIntegralAt_eq_outer, unequalRankIntegralAt_eq_outer]
  have hd : j + 1 + k + 1 = j + (k + 1) + 1 := by omega
  apply integral_congr_ae
  filter_upwards [] with q
  rw [hf₀ q.out, hd]

/-- The reverse transfer preserves all scalar integrals for the same coefficient
and all second functions, assuming the pointwise cutoff construction. -/
theorem exists_reverse_adjacent_integral_coefficient
    [LocallyCompactSpace F] [TotallyDisconnectedSpace F]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (n r j k : ℕ)
    [BorelSpace (Fin (n + 1) → F)] [(rowMeasure ν (n + 1)).IsOpenPosMeasure]
    [BorelSpace (Matrix (Fin (j + 1)) (Fin (n + 1)) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ r π)
    (hs : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F), IsCompact C ∧
        ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C)
    (f : (coefficientModel π ℓ).toSubmodule)
    (hcutoff : ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ f₁ : (coefficientModel π ℓ).toSubmodule, ∀ g X,
        f₁.val.val (blockMatrixAt (j + 1) k h₁ g X) =
          Φ (X (Fin.last j)) * f.val.val (blockMatrixAt (j + 1) k h₁ g X)) :
    ∃ f₁ : (coefficientModel π ℓ).toSubmodule,
      ∀ (f' : InverseWhittakerFunctions ψ n) (s : ℂ),
      unequalRankIntegralAt (j + 1) k h₁ ψ abv μ
          (rectangularMeasure ν (j + 1) (n + 1)) f₁.val f' s =
        unequalRankIntegralAt j (k + 1) h₂ ψ abv μ
          (rectangularMeasure ν j (n + 1)) f.val f' s := by
  obtain ⟨f₁, hf₁⟩ := exists_reverse_adjacent_block_integral_coefficient
    ν n r j k h₁ h₂ ψ π hπ ℓ hs f hcutoff
  refine ⟨f₁, ?_⟩
  intro f' s
  rw [unequalRankIntegralAt_eq_outer, unequalRankIntegralAt_eq_outer]
  have hd : j + 1 + k + 1 = j + (k + 1) + 1 := by omega
  apply integral_congr_ae
  filter_upwards [] with q
  rw [hf₁ q.out, hd]

universe uW

/-- Uniform compact support implies the forward inclusion of actual rational
value sets. The original continuation is retained for the transferred vector. -/
theorem adjacent_values_subset_of_support (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (n r j k : ℕ)
    [BorelSpace (Fin (n + 1) → F)]
    [BorelSpace (Matrix (Fin (j + 1)) (Fin (n + 1)) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ r π)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ' : glInverseFunctionals ψ n σ)
    (hs : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F), IsCompact C ∧
        ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C) :
    unequalRankValuesAt (j + 1) k h₁ q ψ abv μ
        (rectangularMeasure ν (j + 1) (n + 1)) π σ ℓ ℓ' ⊆
      unequalRankValuesAt j (k + 1) h₂ q ψ abv μ
        (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ' := by
  rw [unequalRankValuesAt_eq_set, unequalRankValuesAt_eq_set]
  rintro R ⟨f, f', hf⟩
  obtain ⟨C, hC, hs⟩ := hs f
  obtain ⟨f₀, hf₀⟩ := exists_adjacent_integral_coefficient ν n r j k h₁ h₂
    ψ abv μ π hπ ℓ f C hC hs
  refine ⟨f₀, f', ?_⟩
  have he := funext (hf₀ f'.val)
  rw [← he]
  exact hf

/-- Uniform support and actual same-model cutoff realizability suffice for
adjacent equality of the rational-value sets, hence also of their Laurent spans.
No analytic continuation existence is assumed in this reduction. -/
theorem adjacent_values_eq_of_support_cutoff
    [LocallyCompactSpace F] [TotallyDisconnectedSpace F]
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (n r j k : ℕ)
    [BorelSpace (Fin (n + 1) → F)] [(rowMeasure ν (n + 1)).IsOpenPosMeasure]
    [BorelSpace (Matrix (Fin (j + 1)) (Fin (n + 1)) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (h₁ : r = n + ((j + 1) + k + 1)) (h₂ : r = n + (j + (k + 1) + 1))
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ r π)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ' : glInverseFunctionals ψ n σ)
    (hs : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F), IsCompact C ∧
        ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C)
    (hcutoff : ∀ (f : (coefficientModel π ℓ).toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      ∃ f₁ : (coefficientModel π ℓ).toSubmodule, ∀ g X,
        f₁.val.val (blockMatrixAt (j + 1) k h₁ g X) =
          Φ (X (Fin.last j)) * f.val.val (blockMatrixAt (j + 1) k h₁ g X)) :
    unequalRankValuesAt (j + 1) k h₁ q ψ abv μ
        (rectangularMeasure ν (j + 1) (n + 1)) π σ ℓ ℓ' =
      unequalRankValuesAt j (k + 1) h₂ q ψ abv μ
        (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ' := by
  apply Set.Subset.antisymm
  · exact adjacent_values_subset_of_support ν n r j k h₁ h₂ q ψ abv μ π hπ ℓ σ ℓ' hs
  · rw [unequalRankValuesAt_eq_set, unequalRankValuesAt_eq_set]
    rintro R ⟨f, f', hf⟩
    obtain ⟨f₁, hf₁⟩ := exists_reverse_adjacent_integral_coefficient
      ν n r j k h₁ h₂ ψ abv μ π hπ ℓ hs f (hcutoff f)
    refine ⟨f₁, f', ?_⟩
    have he := funext (hf₁ f'.val)
    rw [he]
    exact hf

end AdjacentIntegral

section PadicAssembly

open Whittaker GeneralLinear

universe uF uV uW

/-- The exact published adjacent-span target reduces to uniform compact support
and Fourier preimages for the supplied Haar. The published smearing theorem
constructs every needed same-model cutoff. -/
theorem adjacentBlockSpan_of_support_fourier {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
    (hsupport : ∀ j k, UnequalRankCompactSupportStatement.{uF,uV} F T n (j + 1) k)
    (hfourier : PadicRowFourierSurjectivityStatement F T (n + 1)) :
    UnequalRankAdjacentBlockSpanStatement.{uF,uV,uW} F T n r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.sigmaCompactSpace
  let := T.secondCountableTopology
  let : NonarchimedeanRing F.Carrier := by
    convert (ValuativeRel.nonarchimedeanRing F.Carrier) using 1
    exact (ValuativeRel.valuation F.Carrier).toTopologicalSpace_eq
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ ψ _ μ _ ν V _ _ W _ _ π σ hπ _ ℓ ℓ' hℓ _ j k hr
  have h₁ : r = n + ((j + 1) + k + 1) := by omega
  have h₂ : r = n + (j + (k + 1) + 1) := by omega
  have hs : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F.Carrier), IsCompact C ∧
        ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C := by
    subst h₁
    exact hsupport j k ψ V π hπ ℓ hℓ
  have hc : ∀ (f : (coefficientModel π ℓ).toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      ∃ f₁ : (coefficientModel π ℓ).toSubmodule, ∀ g X,
        f₁.val.val (blockMatrixAt (j + 1) k h₁ g X) =
          Φ (X (Fin.last j)) * f.val.val (blockMatrixAt (j + 1) k h₁ g X) := by
    subst h₁
    intro f Φ
    obtain ⟨κ, hpair⟩ := hfourier ψ ν Φ
    obtain ⟨f₁, _, hpoint⟩ := unequalRankFourierSmearingStatement F T n j k
      ψ ν V π hπ.1.1 ℓ f κ Φ hpair
    exact ⟨f₁, hpoint⟩
  exact congrArg zetaSpan (adjacent_values_eq_of_support_cutoff
    ν n r j k h₁ h₂ T.residueCardinality ψ (normalizedAbsoluteValue T) μ
    π hπ.1.1 ℓ σ ℓ' hs hc)

/-- The published compact-support theorem discharges the support premise.
Only Fourier preimages for every supplied Haar remain as a hypothesis. -/
theorem adjacentBlockSpan_of_fourier {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ)
    (hfourier : PadicRowFourierSurjectivityStatement F T (n + 1)) :
    UnequalRankAdjacentBlockSpanStatement.{uF,uV,uW} F T n r :=
  adjacentBlockSpan_of_support_fourier F T n r
    (fun j k => unequalRankCompactSupport.{uF,uV} F T n (j + 1) k) hfourier

end PadicAssembly

end Langlands.RankinSelberg.AdjacentBlockReduction

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Adjacent unequal-rank JPSS blocks have equal Laurent spans for every
supplied topology and additive Haar measure. -/
theorem unequalRankAdjacentBlockSpan {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankAdjacentBlockSpanStatement.{uF,uV,uW} F T n r :=
  AdjacentBlockReduction.adjacentBlockSpan_of_fourier F T n r
    (HarmonicAnalysis.padicRowFourierSurjectivity F T (n + 1))

end Langlands.RankinSelberg
