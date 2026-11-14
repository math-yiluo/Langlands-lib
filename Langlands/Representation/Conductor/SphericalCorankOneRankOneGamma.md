# The gamma factor of `π × 1` from its epsilon factor and L-polynomials

Module `Langlands.Representation.Conductor.SphericalCorankOneRankOneGamma`, namespace
`Langlands.Conductor.SphericalCorankOne`. It is an internal helper for the proof of
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement`. The first two results hold
over an arbitrary field. The last one holds over every nonarchimedean local field. No
`PadicField` is involved.

## Statements

- `inverseTransposePullback_rankOneCharacter_one`: the trivial character `1` of `GL_1(F)`,
  seen as the representation `rankOneCharacter 1`, equals its own inverse-transpose pullback.
- `isOfWhittakerType_rankOneCharacter_one ψ`: `rankOneCharacter 1` is of Whittaker type
  (rank index `0`) for the standard character of every unitary additive character `ψ`.
- `isPairGammaFactor_rankOne_of_convergence`: let `F` be a nonarchimedean local field, `q > 1`,
  `δ = q⁻¹`, and let `π` be a representation of `GL_(N+2)(F)`. Assume:
  - `π` is of Whittaker type for `ψ`, and its inverse-transpose pullback `π̃` is of Whittaker
    type for `ψ.scale (-1)`;
  - for every pair of nonzero functionals `ℓ` on `π` and `ℓ'` on `1`, the block integrals
    with `j = 0`, `k = N` of `π × 1` converge on a right half-plane
    (`UnequalRankConvergenceAt 0 N`, measure `rectangularMeasure ν 0 1`). The same holds for
    the dual pair `π̃ × 1̃` with the dual functionals;
  - `(c, m)` is the epsilon factor of `π × 1` (`IsPairEpsilonFactor q ψ abv ν π 1 (c, m)`);
  - `P` is the standard L-polynomial of `π` and `P̃` that of `π̃` for `ψ.scale (-1)`
    (`IsCharacterLPolynomial … 1`).

  Then `rationalGammaExpression δ c m P P̃` is a gamma factor of `π × 1` in the published sense
  `IsPairGammaFactor q ψ abv ν π (rankOneCharacter 1)`.

The convergence hypotheses are part of JPSS 1983, Theorem (2.7)(i). The statement does not
claim them.

## Proofs

- Pullback: extensionality and `simp` with the definitions of `inverseTransposePullback`,
  `characterRepresentation` and `twist`. The trivial character takes the value `1` everywhere.
- Whittaker type: the published `scalar_isOfWhittakerType_rankOne`. Every vector of the trivial
  character generates the whole space, and the group acts by scalars.
- Gamma factor: `isPairEpsilonFactor_of_lt` and `isPairGammaFactor_of_lt` unfold both notions
  for ranks `1 < N+2`. The measure and functional existence parts are copied. Fix a compatible
  quotient measure `μ` and nonzero `ℓ`, `ℓ'`. The published `unipotentQuotientHaar_unique`
  identifies `μ` with `rankOneQuotientHaar F`. The epsilon definition gives `ζ` and two
  polynomials `P₀`, `P̃₀` that generate, for every block `(j, k)`, the ideals of the block
  integrals and of the dual block integrals, and satisfy the epsilon equation.
  - `P₀ = P`: the published `HighlyRamified.characterZetaValues_succ_eq` rewrites the hypothesis
    on `P` as a normalized generator of the block `(0, N)` zeta values. By the published
    `UnequalRankConvergenceAt.isNormalizedGenerator_iff` with `hC`, `P` is then also a
    normalized generator of the block `(0, N)` rational values, as `P₀` is. Normalized
    generators are unique.
  - `P̃₀ = P̃`: the dual statement at block `(N, 0)` is rewritten by the published
    `dualUnequalRankRationalValuesAt_eq` into the block `(0, N)` values of the dual pair. Then
    the same argument applies, with `hCd`, the dual Whittaker type and
    `firstDualFunctional_ne_zero`, `secondDualFunctional_ne_zero`. The pullback lemma above
    replaces `1̃` by `1` when needed.
  - The published `UnequalRankEpsilonEquation.gammaEquation` turns the epsilon equation and the
    generator data into the gamma equation for `rationalGammaExpression δ c m P P̃`.

## Provenance

The identity `γ(s, π × σ, ψ) = ε(s, π × σ, ψ) L(1 - s, π̃ × σ̃) / L(s, π × σ)` is
Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983),
Theorem (2.7)(iii), printed page 390. Here `σ` is the trivial character of `GL_1`. The Lean proof
is internal. It works block by block and does not use `IsPairLPolynomial`.
