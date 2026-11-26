# Transitivity of constant terms on standard parabolic quotients

For standard parabolics `Q ≤ P ≤ R`, `constantTerm_constantTerm_of_parabolicQuotient`
proves `C_Q(C_P f) = C_Q f` for each continuous function `f` on the parabolic quotient
`U_R(𝔸) M_R(F) \ G(𝔸)`. It uses the same two normalized radical quotient measures as the
Library's constant terms. This is the transitivity identity in Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series* (2024), §6.2, in the paragraph defining
`C_{P,Q}` after (6.5).

The invariant function on the `R` quotient is fixed by the rational points of `Q` by
`isLeftInvariantUnder_rationalImage_of_le`. This permits applying
`constantTerm_constantTerm_of_le_of_rationalParabolicInvariant`. Its proof descends
`v ↦ f(v g)` to the compact rational quotient of `U_Q` and averages over `U_P`, which is
normalized by `U_Q`. The compact quotient average preserves the outer integral. At a
representative `v` the fiber integral is `C_P f(v g)`.

The source locator uses the journal PDF, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`, SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`, printed p. 201. The source
states the identity for `f` on `G(F) \ G(𝔸)`. The proof on the parabolic quotient uses the same
averaging identity because descent at the fixed argument only needs invariance under the rational
points of `U_Q`.

## Integration on rational quotients

- `AdelicSubgroupPoints.invariantIntegrand V f hf g`: for `f` invariant under the rational points
  of a subgroup functor `V`, the function `n ↦ f(n g)` on `V(𝔸)` descended to `V(F) \ V(𝔸)`;
  `invariantIntegrand_mk`, `invariantIntegrand_out` and `continuous_invariantIntegrand` give its
  values and continuity.
- `AdelicSubgroupPoints.integral_iterated_invariantIntegrand`: for `U ≤ V` with `U` normalized by
  `V`, both rational quotients compact, and `f` continuous and invariant under the rational points
  of `V`, the iterated average over `V(F) \ V(𝔸)` of the averages over `U(F) \ U(𝔸)` is the
  average over `V(F) \ V(𝔸)`. The proof is that of
  `integral_normalizedConstantTerm_eq_of_isNormalizedBy`: the compact subgroup averaging identity
  `LeftCosetSpace.integral_compactSubgroupAverage`, with conjugation by rational points of `V`
  preserving the normalized measure on `U(F) \ U(𝔸)`.
- `StandardParabolicFamily.rationalImage_radical_le_parabolicQuotientSubgroup`: for `Q ⊆ R` the
  rational points of `U_Q` lie in `U_R(𝔸) M_R(F)`.
