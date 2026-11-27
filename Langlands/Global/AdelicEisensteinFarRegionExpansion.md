# Cuspidal expansions of a far-region Eisenstein comparison

Module `Langlands.Global.AdelicEisensteinFarRegionExpansion`, for a standard family `fam`.

## Padded decompositions and twisted tests

- `isExponentDecomposition_sub`: exponent decompositions of `f` on `s` and of `h` on `t`
  give one of `f − h` on `s ∪ t`, with components extended by zero. Automorphic functions
  form a submodule, and `isCuspidalAlong_sub` and `hasUnnormalizedExponent_sub` preserve
  the remaining clauses.
- `leviPairing_constantTerm_eq_sum_of_projection`: the test of `C_J f` equals the test of a
  cuspidal projection, by the pairing clause of `IsCuspidalProjection`. It is therefore
  the sum of the tests of the components of an exponent decomposition.
- For `J ≤ Q`, the test of a twist by the height of `P_Q` is the test times the height
  factor at the external argument, and twisting preserves absolute convergence of the
  tests: `leviPairing_parameterTwist_of_le` and `parameterTwist_mem_leviPairingDomain` of
  `Langlands.Global.AdelicCuspidalTestAlgebra`.

## `pBracket_isJointlySupportedIn`

Consider the bracket
`g ↦ (C_J E (· g), ψ) − (C_{Q,J}(∑ i, a i · ψ i)_μ (· g), ψ)`. Suppose that in every finite
joint generalized eigendecomposition of it, the components outside a set `S` of
characters vanish. Then the bracket is supported in `S`. The decomposition used is
explicit:

- the tests of the components of an exponent decomposition of the cuspidal projection of
  `C_J E`;
- minus, when `J ≤ Q`, the coefficient multiples of the tests of the twists of the
  components of the cuspidal projections of `C_J ψ i`. These have exponents `ν + res μ`.
  When `J` is not contained in `Q`, the second term is zero.

The conclusion follows from `isJointlySupportedIn_of_fiberVanishing_sub` and
`isJointlySupportedIn_of_fiberVanishing` of `Langlands.Global.AdelicJointExponentSupport`.

## `exists_expansion_of_supported`

Let `left` and `right` be cuspidal projections of `C_J E_P` and `C_J E_Q`, with exponent
decompositions. Let `ref` be a common reference test. Suppose the tests of `C_J E_P − ref`
and `C_J E_Q − ref` are supported in the characters of `ΛP` and `ΛQ`, and every exponent in
`ΛP ∪ ΛQ` satisfies a predicate `Good`. Then `left = right + ∑ ν ∈ u, b ν`. Here each
`b ν` has unnormalized exponent `ν` and `Good ν` holds. The test of `left − right` is the
difference of the two brackets, so it is supported in `ΛP ∪ ΛQ`.
`exponentDecomposition_eq_zero_of_tests` removes every component of the padded
decomposition of `left − right` whose exponent is outside `ΛP ∪ ΛQ`. Cusp detection and
integrability are hypotheses. The remaining components form the sum. This is the form of
the expansion hypothesis of `eq_of_weyl_cuspidal_expansions`.

These are derived steps of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series* (2024), §8.6. They use (6.8), (6.10) and (6.20).
