import Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroIntegralLaws
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Determinant-slice expansion of the actual unequal-rank integrals

For a p-adic field, every quotient measure and every rectangular measure, absolute
convergence of the actual unequal-rank JPSS integral at `s` makes its slice coefficients
at zero absolutely summable against `(q^(-s))^m`, with sum the integral at `s`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Slices

variable {n : ℕ} (j k : ℕ)

/-- The slice coefficient of the unequal-rank integral: the restricted integral over the
determinant slice `m` of the inner rectangular integral at `s = 0`. -/
def unequalRankSliceCoefficient
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (μ : letI := T.topology
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier)]
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
    (W : letI := T.topology; WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : letI := T.topology; InverseWhittakerFunctions ψ n) (m : ℤ) : ℂ :=
  letI := T.topology
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  ∫ q in determinantSlice T n m,
    ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k W W' 0 x q ∂ν ∂μ

/-- On the determinant slice `m`, the unequal-rank integrand at `s` is its value at zero
times `(q^(-s))^m`. -/
theorem unequalRankIntegrand_eq_mul_spectralPoint_zpow :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (W : WhittakerFunctions ψ (n + (j + k + 1)))
      (W' : InverseWhittakerFunctions ψ n) (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
      (m : ℤ) (q : LeftUnipotentQuotient n F.Carrier), q ∈ determinantSlice T n m →
      unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k W W' s x q =
        unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k W W' 0 x q *
          spectralPoint T.residueCardinality s ^ m := by
  let := T.topology
  intro ψ W W' s x m q hq
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hq
    rw [unequalRankIntegrand_mk, unequalRankIntegrand_mk]
    have hexp : s - ((j + k + 1 : ℕ) : ℂ) / 2 = (0 - ((j + k + 1 : ℕ) : ℂ) / 2) + s := by ring
    have hw : determinantWeight (normalizedAbsoluteValue T) g s =
        spectralPoint T.residueCardinality s ^ m := by
      rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
      change T.ord (Matrix.det g.val) = m at hq
      rw [hq]
    rw [hexp, determinantWeight_exponent_add, hw]
    ring

/-- At a parameter of absolute convergence, the actual unequal-rank integral is the
absolutely summable series of its slice coefficients against `(q^(-s))^m`. -/
theorem unequalRank_sliceExpansion :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)) [SFinite μ]
      [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier)]
      (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier)) [SFinite ν]
      (W : WhittakerFunctions ψ (n + (j + k + 1))) (W' : InverseWhittakerFunctions ψ n)
      (s : ℂ),
      UnequalRankConverges ψ (normalizedAbsoluteValue T) j k μ ν W W' s →
      Summable (fun m : ℤ => ‖unequalRankSliceCoefficient T j k ψ μ ν W W' m *
          spectralPoint T.residueCardinality s ^ m‖) ∧
        HasSum (fun m : ℤ => unequalRankSliceCoefficient T j k ψ μ ν W W' m *
          spectralPoint T.residueCardinality s ^ m)
          (unequalRankIntegral ψ (normalizedAbsoluteValue T) j k μ ν W W' s) := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ μ _ _ ν _ W W' s hs
  have hG : Integrable (fun q => ∫ x,
      unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k W W' s x q ∂ν) μ :=
    hs.integral_prod_left
  have heq : ∀ m : ℤ,
      (∫ q in determinantSlice T n m, ∫ x,
          unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k W W' s x q ∂ν ∂μ) =
        unequalRankSliceCoefficient T j k ψ μ ν W W' m *
          spectralPoint T.residueCardinality s ^ m := by
    intro m
    rw [setIntegral_congr_fun (measurableSet_determinantSlice T n m) (g := fun q =>
        (∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k W W' 0 x q ∂ν) *
          spectralPoint T.residueCardinality s ^ m) (fun q hq => by
      dsimp only
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
        unequalRankIntegrand_eq_mul_spectralPoint_zpow T j k ψ W W' s x m q hq)),
      integral_mul_const]
    rfl
  have hsum := hasSum_setIntegral_determinantSlice T μ hG
  simp only [heq] at hsum
  exact ⟨by simpa only [heq] using summable_norm_setIntegral_determinantSlice T μ hG, hsum⟩

end Slices

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
