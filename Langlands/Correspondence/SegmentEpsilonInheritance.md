# Segment-pair epsilon inheritance from the segment-head factor formulas

Author: Worker 1695.

This module proves `SegmentPairEpsilonCompatibility` and
`SupercuspidalSegmentPairInheritance` (module `AssemblyEpsilonReduction`) from
explicit published premises. As a corollary it proves the target proposition
`AssemblyEpsilonInheritanceStatement` from those premises together with
multisegment datum matching. No premise is proved here. The premises are:

- `RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}` (Henniart 2002, §2.6,
  first display);
- `RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA}` (Henniart 2002,
  §2.6, third display);
- `LocalFactor.PairBlock.BlockPairGamma.{uF, uP} F` (Henniart 2002, §2.4);
- either `ArithmeticBlockPairLFactor.{uF, uP} F` (module
  `AssemblyLSegmentReduction`) or `WDEulerPairBlockStatement.{0, uF, uP, uP}`.
  The second implies the first by `arithmeticBlockPairLFactor_of_wdEulerPairBlock`
  (module `AssemblyBlockPairEuler`);
- for the final corollary only, `MultisegmentHeadDatumMatching.{uF, uA} F`.

The contragredient segment L-formula `SegmentHeadContragredientLFactorStatement`
is not used. Only the standard axioms are used.

Notation: `ω = (localNormCharacter F).toMonoidHom`, `δ = residueReflection F`,
`q` the residue cardinality. `T` is the local tensor of the uncentered blocks
`B ⊗ Sp(a+1)` and `B' ⊗ Sp(b+1)`, and `L_k = zm(ω^k B) ⊗ zm(B')`. `LR` is the
reflected L-ratio at the local inertia and the published geometric Frobenius
(module `SegmentGaloisGamma`).

## Twisted supercuspidal gamma factors

`IsSupercuspidalCorrespondence.exists_twistedPairGamma`: let `c0` be a
supercuspidal correspondence compatible with pair factors for the system
`(eC, ε, hε)`. Let `B`, `B'` represent `σ`, `τ`, let `A`, `A'` be supercuspidal
representatives of `c0 σ`, `c0 τ`, and let `k : ℕ`. Then some `e = (c, m)`
satisfies both:
- `IsArithmeticPairEpsilonFactor` for the classes of `zm(ω^k B)` and `zm(B')`;
- `IsPadicSymmetricGammaFactor F ψ ν (ν^k A) A' (c X^m · LR(L_k))`, where
  `ν^k A = realPowerTwist (determinantNorm (d+1)) k A`.

Proof. As in the published `twistedSupercuspidalPairLCompatibility` (module
`AssemblyLTwistedSupercuspidal`):
- twist compatibility with the quasi-character `|·|^k` identifies
  `c0 (ω^k σ)` with the class of `ν^k A`;
- the published `supercuspidalGammaFromFactors`, applied to the pair-factor
  compatibility of the given system and to dual compatibility, gives the gamma
  factor of `(c0 (ω^k σ), c0 τ)`;
- the arithmetic gamma factor of `(ω^k σ, τ)` is the epsilon monomial times
  `LR(L_k)`.

## Main theorem

`segmentPairEpsilonCompatibility_of_segmentHeads hL hG hBPG hB hc0 hcompat`
proves `SegmentPairEpsilonCompatibility F eC ε hε c0`. Fix `ψ`, a self-dual `ν`,
`σ`, `τ` with representatives `B`, `B'`, and segment-head models `Q`, `Q'` of
`Δ = segmentOf c0 σ a` and `Δ' = segmentOf c0 τ b`. The proof has seven steps.

1. **L-polynomial.** The published `segmentPairLCompatibility_of_segmentHeads`
   gives `P` with `IsPadicRankLPolynomial Q Q' P` and
   `arithmeticPairLFactor(T) = 1/P`. So the local Euler polynomial of `T` is `P`.
2. **Representation side.** `exists_segmentHead_rationalGammaExpression` (module
   `SegmentHeadGammaExpression`) gives `e`, `P`, `D` (with `D(0) = 1`) and `H`:
   `e` is the epsilon factor of the segment heads, and
   `rationalGammaExpression δ e P D = ∏_i ∏_j H i j`, with `H i j` the gamma
   factor of `(ν^(i+j) A, A')`. Step 1 and L-uniqueness identify the two `P`.
   The epsilon relation transfers from the heads to `Q`, `Q'` by
   `IsPadicRankEpsilonFactor.congr_equiv`.
3. **Twisted factors.** By `exists_twistedPairGamma` and gamma uniqueness,
   `H i j = c_(i+j) X^(m_(i+j)) · LR(L_(i+j))`, where `(c_k, m_k)` is the
   arithmetic epsilon factor of `L_k`.
4. **Admissible data.** The first certificate (`k = 0`) supplies the base
   character, a self-dual measure and a geometric Frobenius. The blocks of the
   lifted restrictions give admissible continuous base data for the classes of
   the blocks of `B` and `B'`.
5. **Epsilon value at given data.** Take arbitrary admissible data `ψ'`, `μ`,
   `X`, `Y`, `Φ`, `s`. Transport the epsilon value to the bottom-field blocks.
   By `conditionalPairEpsilonValue_baseBlock` and the `k`-certificates at the
   twisted factors (admissible by `restrictTwistedBaseEquiv` and
   `restrictZeroBaseEquiv`), it is `epsilonMonomial q C M s` with
   `C = (∏ c_(i+j)) · c_Φ` and `M = Σ m_(i+j) + d_Φ`. Here `c_Φ X^(d_Φ)` is the
   quotient correction at `Φ`.
6. **Gamma identity.** By `rationalLRatio_localBlockTensor` at `Φ`,
   `∏∏ H i j = rationalGammaExpression δ C M P P_(T^∨)`.
7. **Cancellation.** Step 2 gives
   `rationalGammaExpression δ e P D = rationalGammaExpression δ C M P P_(T^∨)`.
   Here `P ≠ 0` and `D(0) = P_(T^∨)(0) = 1`, so `rationalGammaExpression_cancel`
   gives `e = (C, M)`.

## Corollaries

- `supercuspidalSegmentPairInheritance_of_segmentHeads hL hG hBPG hB`:
  `SupercuspidalSegmentPairInheritance.{uF, uP, uA} F`.
- `supercuspidalSegmentPairInheritance_of_segmentHeads_of_wdEuler hL hG hBPG hE`:
  the same, with `hE : WDEulerPairBlockStatement.{0, uF, uP, uP}`.
- `SegmentEpsilonReductionStatement F` (definition, a proposition): the
  implication `SegmentHeadLFactorStatement.{uF, uA, uA} →
  SegmentHeadGammaFactorStatement.{uF, uA, uA} → BlockPairGamma.{uF, uP} F →
  WDEulerPairBlockStatement.{0, uF, uP, uP} →
  SupercuspidalSegmentPairInheritance.{uF, uP, uA} F`. The theorem
  `segmentEpsilonReduction` proves it from the previous corollary.
- `assemblyEpsilonInheritance_of_segmentHeads hP hL hG hBPG hE`:
  `AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F`. It combines the previous
  corollary with the published
  `assemblyEpsilonInheritance_of_datumMatching_and_segmentPairs` (module
  `AssemblyEpsilonRemainingReduction`).

## Provenance

The segment-pair factor formulas of Henniart 2002
(`henniart-2002-characterization`), §2.6, printed page 595, and the block-pair
gamma law, §2.4, enter only as the published hypotheses listed above. The
argument comparing the two gamma expressions and cancelling the L-ratios is
derived. In particular, the dual L-polynomials need not be matched: their
constant terms equal `1`, which suffices.
