# Proof of the regular-patch Eisenstein comparison for finite families of inducing data

Module `Langlands.Global.AdelicEisensteinStandardFamilyComparisonProof` proves
`Langlands.Global.StandardEisensteinFamilyComparisonReductionStatement`, as
`Langlands.Global.standardEisensteinFamilyComparisonReduction`. Five published statements
together imply `StandardEisensteinFamilyComparisonStatement`:

- `EisensteinMeromorphicContinuationStatement` (continuation, Bernstein–Lapid Theorem 2.3 (1));
- `LeadingCuspidalInjectivityStatement` (Theorem 6.3);
- `ConvergentCuspidalTestExpansionStatement` ((6.20) in the region of convergence);
- `CuspidalProjectionDecompositionStatement` (cuspidal projections and their exponent
  decompositions);
- `LeviCuspFormPairingMajorantStatement` (integrable majorants of Levi cusp forms).

The work is done by `StandardParabolicFamily.standardFamilyComparison_of_inputs`, for a closed
matrix embedding of positive size. The reduction first replaces an embedding of size zero by a
positive-size one with the same automorphic functions
(`exists_positiveMatrixEmbedding_of_isClosedSubgroup`). The conclusion does not mention the
embedding.

The module also proves `standardEisensteinRegularComparison_of_family`:
`StandardEisensteinFamilyComparisonStatement` implies
`StandardEisensteinRegularComparisonStatement` (module
`Langlands.Global.AdelicEisensteinStandardRegularComparisonStatement`). The single form is the
family with one member `φ`, the coefficient `1` and coefficient domain the whole space.

## Proof of `standardFamilyComparison_of_inputs`

Write `P = P_I`, `Q = P_Q`, `w` for the Weyl element of `n`, and `wλ` for
`weylParameter (l I) c proj λ`. The data are inducing forms `φ v` with meromorphic coefficients
`b v`, the function `EP` equal to `∑ v, b v λ · E(φ v, λ)` for regular `λ`, and the forms `ψ i`
with coefficients `coeff i` such that `∑ v, b v λ · M(w, λ)(φ v) = ∑ i, coeff i λ · ψ i` for
regular `λ`.

1. **Coordinates.** Take coordinates `e : ℂᵐ ≃ X^*(P) ⊗ ℂ` from a basis. Weyl transport is a
   linear equivalence (`exists_weylParameter_linearEquiv`), so `eQ = wE ∘ e` is a coordinate
   system on `X^*(Q) ⊗ ℂ` with `eQ x = w(e x)`.
2. **Continuations.** `EisensteinMeromorphicContinuationStatement` gives a continuation `Ev v` of
   each `E(φ v, ·)`, and continuations `EQc i` of the `Q`-series of the `ψ i`.
   `exists_openDense_continuation_tests` gives open dense sets `Uv v` (for `Ev v ∘ e`) and `UQ i`
   (for `EQc i ∘ eQ`) on which the values are automorphic and, for `Ev v`, all norm-one Levi tests
   of constant terms are meromorphic. Put `U = ⋂ v, Uv v`. Let `Dbz` and `Dc` be the domains of
   the coefficients `b v ∘ e` and `coeff i ∘ e`. The combined continuation is
   `E' λ = ∑ v, b v λ · Ev v λ`. It is automorphic on `e(U)` and pointwise meromorphic on
   `U ∩ Dbz`. The given `EP` agrees with `E'` on `e⁻¹ DP ∩ U ∩ Dbz`. Both are meromorphic and
   equal to `∑ v, b v λ · E(φ v, λ)` on a regular region, so the scalar identity theorem
   (`IsMeromorphicOn.eqOn_of_eqOn_open`) applies at every `g`.
3. **Competing data.** For every standard `J`,
   `exists_competingWeylExponents_continued_support_family` (module
   `Langlands.Global.AdelicEisensteinFamilyFarRegionSupport`) gives `P`-side labels
   `(dataP J).label j λ`. Their support property holds on `U ∩ Dbz ∩ Dc`.
   `exists_identityWeyl_support` gives a threshold `RQJ J` and `Q`-side labels
   `(dataQ J i).label j μ`. The finitely many constant parts of all labels form a finite set `S`
   of shifts in `𝔞₀^*`. The standard indices are finite.
4. **Region of comparison.** `O₀` is the set of `x ∈ U ∩ Dbz ∩ Dc ∩ ⋂ UQ i` with `eQ x` regular
   beyond all thresholds `RQJ J` and the agreement thresholds of the `EQc i`. Put
   `EQ λ = ∑ i, coeff i λ · E(ψ i, wλ)`. On `e(O₀)` each `E(ψ i, wλ)` equals the automorphic
   value `EQc i (eQ x)`, so `EQ` and `E'` are automorphic there.
5. **Expansions.** Fix `λ = e x` with `x ∈ O₀`, and a standard `J`.
   `CuspidalProjectionDecompositionStatement` gives cuspidal projections `left` of `C_J E' λ` and
   `right` of `C_J EQ λ`, with exponent decompositions. The tests of both are compared with the
   common reference `(C_{Q,J}(∑ i, coeff i λ · ψ i)_{wλ}, ψ)`.
   - `pBracket_isJointlySupportedIn` gives support of the `P`-side bracket in the `P`-labels at
     `λ`.
   - `exists_identityWeyl_support` gives support of the `Q`-side bracket in the `Q`-labels at
     `wλ`.
   - Cusp detection (`eq_zero_of_leviPairings_eq_zero`) and integrability
     (`mem_leviPairingDomain_of_isAutomorphicOn_of_majorant`, using the majorant) let
     `exists_expansion_of_supported` write `left = right + ∑ b ν`.

   Every exponent there is a competing label of one of two forms. A `P`-label has
   `Re = v · Re λ + shift` with `v ≠ w` positive on `I`. A `Q`-label has
   `Re = v' · Re wλ + shift = (v' w) · Re λ + shift` with `v' ≠ 1` positive on `Q`, by the
   ambient transport `eisensteinAmbientWeylParameter`. Then `v' w ≠ w`, and `v' w` is positive on
   `I` because `w(I) ⊆ Q`.
6. **Comparison.** `eq_of_weyl_cuspidal_expansions` uses Weyl separation with the finite shift set
   `S` and `LeadingCuspidalInjectivityStatement`. It gives a bound `Rnl` such that `E' λ = EQ λ`
   on `e(O₀)` wherever `wλ` is `Rnl`-regular.
7. **Patch.** `O` is the set of `x ∈ U ∩ Dbz ∩ Dc ∩ ⋂ UQ i ∩ e⁻¹ DP` with `eQ x` regular beyond
   `max RQall (max R Rnl)`. It is open. It is nonempty because the regular region in the
   coordinates `eQ` is open and nonempty and the other sets are open and dense
   (`dense_iInter_of_isOpen`). On `O`, `EP (e x) = E' (e x) = EQ (e x)`, which is the conclusion.

## Relation to the source

This implements the proof of J. Bernstein and E. Lapid, *On the meromorphic continuation of
Eisenstein series*, J. Amer. Math. Soc. 37 (2024), Theorem 2.3 (4), §8.6, p. 225, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, in their standard setting, applied to
the inducing datum `∑ v, b v λ · φ v`. The identity of the leading cuspidal components of the
continued `P`-series and of `E(M(w, λ)φ, wλ)` far in the `w`-chamber is derived from Lemma 6.8 and
(6.20) for the first, and from Proposition 6.9 (identity Weyl element) for the second.
Bernstein–Lapid continue the formula (6.18) for `E(φ, λ)` by continuing each intertwining operator
`M(v, λ)`. The Lean proof instead continues the support of the tested difference by
`meromorphicExponentSupport`, so it uses (6.20) only in the region of convergence. Theorem 6.3 then
identifies the two automorphic forms.
