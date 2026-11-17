import Langlands.Representation.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement
import Langlands.Representation.RankinSelberg.UnitaryEqualRankAnalytic
import Langlands.Representation.RankinSelberg.UnitaryZeroRowAnalytic
import Langlands.Representation.RankinSelberg.BoundaryRationalRegularity
import Langlands.Representation.RankinSelberg.SquareIntegrableLPolynomialNonvanishingProof
import Langlands.Representation.RankinSelberg.NormalizedGeneratorRegularityProof

/-!
# Getz–Hahn Theorem 11.5.2, p-adic case

Every symmetric pair L-polynomial `P` of two unitary generic representations of
`GL_(r+1)(F)` and `GL_(t+1)(F)` over a p-adic field satisfies `P(q^(-s)) ≠ 0` for
`Re(s) ≥ 1`.

The proof follows the route of the statement Markdown and of the published square-integrable
case `squareIntegrableLPolynomialNonvanishing`:

1. a compatible quotient measure for which `P` is the normalized generator of the
   zeta-value sets;
2. absolute convergence of the generating integrals on `Re(s) ≥ 1` and holomorphy on
   `Re(s) > 1` (`unitaryEqualRankAnalytic`, `unitaryZeroRowAnalytic`);
3. boundedness of these integrals on the strip `1 ≤ Re(s) ≤ 2`
   (`norm_integral_cpow_le_of_strip`) and the boundary regularity of their rational
   continuations (`denom_ne_zero_of_bounded_continuation`);
4. `IsNormalizedGenerator.eval_ne_zero_of_regularAt`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnitaryGeneric

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

/-! ### Strip bounds for the two families of integrals -/

section StripBounds

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- An equal-rank integral converging at `s = 1` and `s = 2` is bounded on the strip
`1 ≤ Re(s) ≤ 2`. -/
theorem equalRank_strip_bounded
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (h1 : EqualRankConverges ψ abv μ W W' Φ 1)
    (h2 : EqualRankConverges ψ abv μ W W' Φ 2) :
    ∃ B : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → ‖equalRankIntegral ψ abv μ W W' Φ s‖ ≤ B := by
  let c := equalRankIntegrand ψ abv W W' Φ 0
  let d := quotientDeterminantAbs abv n
  have hd : ∀ q, 0 < d q := quotientDeterminantAbs_pos abv n
  have hfactor (s : ℂ) : equalRankIntegrand ψ abv W W' Φ s =
      fun q => c q * (d q : ℂ) ^ (s - ((0 : ℝ) : ℂ)) := by
    funext q
    rw [Complex.ofReal_zero, sub_zero]
    exact equalRank_integrand_eq_mellin ψ abv W W' Φ s q
  have hi1 : Integrable (fun q => c q * (d q : ℂ) ^ ((1 : ℂ) - ((0 : ℝ) : ℂ))) μ := by
    have h : Integrable (equalRankIntegrand ψ abv W W' Φ 1) μ := h1
    rwa [hfactor] at h
  have hi2 : Integrable (fun q => c q * (d q : ℂ) ^ ((2 : ℂ) - ((0 : ℝ) : ℂ))) μ := by
    have h : Integrable (equalRankIntegrand ψ abv W W' Φ 2) μ := h2
    rwa [hfactor] at h
  refine ⟨∫ q, (‖c q * (d q : ℂ) ^ ((1 : ℂ) - ((0 : ℝ) : ℂ))‖ +
      ‖c q * (d q : ℂ) ^ ((2 : ℂ) - ((0 : ℝ) : ℂ))‖) ∂μ, fun s hs1 hs2 => ?_⟩
  have hb := norm_integral_cpow_le_of_strip μ c d hd 0 hi1 hi2 s hs1 hs2
  unfold equalRankIntegral
  rw [hfactor s]
  exact hb

/-- A zero-row integral converging at `s = 1` and `s = 2` is bounded on the strip. -/
theorem zeroRow_strip_bounded [MeasurableSpace F]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (h1 : UnequalRankConverges ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' 1)
    (h2 : UnequalRankConverges ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' 2) :
    ∃ B : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 →
      ‖unequalRankIntegral ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' s‖ ≤ B := by
  let r : ℝ := ((0 + k + 1 : ℕ) : ℝ)
  let c := unequalRankIntegrand ψ abv 0 k W W' (r / 2 : ℝ) 0
  let d := quotientDeterminantAbs abv n
  have hd : ∀ q, 0 < d q := quotientDeterminantAbs_pos abv n
  have hfactor (s : ℂ) : unequalRankIntegrand ψ abv 0 k W W' s 0 =
      fun q => c q * (d q : ℂ) ^ (s - ((r / 2 : ℝ) : ℂ)) := by
    funext q
    exact zeroRow_integrand_mellin ψ abv k W W' s q
  have hi1 : Integrable (fun q => c q * (d q : ℂ) ^ ((1 : ℂ) - ((r / 2 : ℝ) : ℂ))) μ := by
    have h := (zeroRow_converges_iff ψ abv k μ ν W W' 1).1 h1
    rwa [hfactor] at h
  have hi2 : Integrable (fun q => c q * (d q : ℂ) ^ ((2 : ℂ) - ((r / 2 : ℝ) : ℂ))) μ := by
    have h := (zeroRow_converges_iff ψ abv k μ ν W W' 2).1 h2
    rwa [hfactor] at h
  refine ⟨∫ q, (‖c q * (d q : ℂ) ^ ((1 : ℂ) - ((r / 2 : ℝ) : ℂ))‖ +
      ‖c q * (d q : ℂ) ^ ((2 : ℂ) - ((r / 2 : ℝ) : ℂ))‖) ∂μ, fun s hs1 hs2 => ?_⟩
  have hb := norm_integral_cpow_le_of_strip μ c d hd (r / 2) hi1 hi2 s hs1 hs2
  rw [zeroRow_integral, hfactor s]
  exact hb

end StripBounds

/-! ### The ordered pair and the symmetric relation -/

variable {p : ℕ} [Fact p.Prime]

section Pair

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r t : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
  {P : ℂ[X]}

/-- Every existing ordered-pair L-polynomial of two irreducible admissible unitarizable
representations has no zero at `q^(-s)` for `Re(s) ≥ 1`. -/
theorem eval_ne_zero_of_unitary_pair
    (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hπa : letI := F.canonicalTopologicalData.topology; IsAdmissible π)
    (hπi : Representation.IsIrreducible π) (hπu : IsUnitarizable π)
    (hσa : letI := F.canonicalTopologicalData.topology; IsAdmissible σ)
    (hσi : Representation.IsIrreducible σ) (hσu : IsUnitarizable σ)
    {s : ℂ} (hs : 1 ≤ s.re) :
    P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality s) ≠ 0 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := hP
  have hPair := hP μ hμ
  have hq := PadicField.TopologicalData.residueCardinality_gt_one
    F.canonicalTopologicalData
  have hz0 : spectralPoint F.canonicalTopologicalData.residueCardinality s ≠ 0 :=
    spectralPoint_ne_zero_of_pos (lt_trans Nat.zero_lt_one hq) s
  by_cases htr : t < r
  · obtain ⟨k, hr⟩ : ∃ k : ℕ, r = t + (0 + k + 1) := ⟨r - t - 1, by omega⟩
    subst r
    have hgen := hPair.isUnequalRankLPolynomial 0 k
    apply hgen.eval_ne_zero_of_regularAt hz0
    intro R hR
    rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, _, hR⟩
    have hA := unitaryZeroRowAnalytic F t k ψ μ hμ ν V W π σ hπa hπi hπu hσa hσi hσu
      ℓ ℓ' ⟨f, hf⟩ ⟨f', hf'⟩
    obtain ⟨B, hB⟩ := zeroRow_strip_bounded ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) k μ ν f f'
      (hA.1 1 (by simp)) (hA.1 2 (by norm_num))
    exact denom_ne_zero_of_bounded_continuation hq _ R hA.2 hR B
      (fun s' h1 h2 => hB s' h1.le h2.le) s hs
  · by_cases hrt : r = t
    · subst r
      have hgen := isPairLPolynomial_self.mp hPair
      apply hgen.eval_ne_zero_of_regularAt hz0
      intro R hR
      rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, Φ, _, hR⟩
      have hA := unitaryEqualRankAnalytic F t ψ μ hμ V W π σ hπa hπi hπu hσa hσi hσu
        ℓ ℓ' ⟨f, hf⟩ ⟨f', hf'⟩ Φ
      obtain ⟨B, hB⟩ := equalRank_strip_bounded ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ f f' Φ
        (hA.1 1 (by simp)) (hA.1 2 (by norm_num))
      exact denom_ne_zero_of_bounded_continuation hq _ R hA.2 hR B
        (fun s' h1 h2 => hB s' h1.le h2.le) s hs
    · exact (not_isPairLPolynomial_of_lt (by omega) hPair).elim

/-- The symmetric rank convention. -/
theorem eval_ne_zero_of_unitary_symmetric
    (hP : IsPadicSymmetricLPolynomial F ψ ν π σ P)
    (hπa : letI := F.canonicalTopologicalData.topology; IsAdmissible π)
    (hπi : Representation.IsIrreducible π) (hπu : IsUnitarizable π)
    (hσa : letI := F.canonicalTopologicalData.topology; IsAdmissible σ)
    (hσi : Representation.IsIrreducible σ) (hσu : IsUnitarizable σ)
    {s : ℂ} (hs : 1 ≤ s.re) :
    P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality s) ≠ 0 := by
  by_cases htr : t ≤ r
  · exact eval_ne_zero_of_unitary_pair ((isPadicSymmetricLPolynomial_of_le htr).mp hP)
      hπa hπi hπu hσa hσi hσu hs
  · exact eval_ne_zero_of_unitary_pair
      ((isPadicSymmetricLPolynomial_of_lt (Nat.lt_of_not_ge htr)).mp hP)
      hσa hσi hσu hπa hπi hπu hs

end Pair

/-- **Getz–Hahn, Theorem 11.5.2, p-adic case.** For generic unitarizable representations
`π`, `σ` of `GL_(r+1)(F)` and `GL_(t+1)(F)`, every symmetric pair L-polynomial `P` satisfies
`P(q^(-s)) ≠ 0` for every `s` with `Re(s) ≥ 1`. -/
theorem unitaryGenericLPolynomialNonvanishing :
    UnitaryGenericLPolynomialNonvanishingStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t V _ _ W _ _ π σ hπg hπu hσg hσu P hP s hs
  exact eval_ne_zero_of_unitary_symmetric hP hπg.2.1 hπg.1 hπu hσg.2.1 hσg.1 hσu hs

end Langlands.RankinSelberg.UnitaryGeneric
