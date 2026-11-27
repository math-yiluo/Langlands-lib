# Norm-one Levi tests of automorphic functions on a standard parabolic quotient

Module `Langlands.Global.AdelicLeviPairingAutomorphicTests` concerns the norm-one Levi
pairing `fam.leviPairing J f g test` of `Langlands.Global.AdelicLeadingCuspidalComponents`.
For a standard family `fam` and a standard index `J`, it pairs a function `f` on `G(𝔸)`
with a test on `M_J(𝔸)`. This is the pairing of Bernstein–Lapid (6.8).

## Evaluation and integrability

- `leviPairingIntegrand_eq_of_mk`: suppose `f` is invariant under the image of `M_J(F)` and
  the test is invariant under `M_J(F)`. Then the integrand at a class of
  `M_J(F) \ M_J(𝔸)^1` can be evaluated at any representative `x`, as
  `f(ι(x) g) · conj(test(x))`. The proof lifts the product to the quotient by
  `LeftCosetSpace.lift`.
- `leviRational_invariant_of_isAutomorphicOn`: automorphy on `U_J(𝔸) M_J(F) \ G(𝔸)`
  includes invariance under the rational Levi.
- `mem_leviPairingDomain_of_moderateGrowth`: a continuous function of moderate growth that is
  invariant under the image of `M_J(F)` pairs integrably at every `g`. The test must be
  continuous, rationally invariant, and have an integrable weighted majorant
  (`HasLeviPairingMajorant`) at every growth exponent. Moderate growth `‖f(x)‖ ≤ C ‖x‖^r` and
  the majorant at exponent `r` dominate the integrand, evaluated at the representatives
  supplied by the majorant. The integrand is continuous on the quotient by the evaluation
  lemma.
- `mem_leviPairingDomain_of_isAutomorphicOn_of_majorant`: the case of an automorphic function on the
  quotient for `J`, which is continuous, of moderate growth and invariant under the rational
  Levi.

## Exponents and linearity

- `leviPairing_mem_jointGenEigenspace`: if `f` has unnormalized exponent `λ` along `J` and
  pairs integrably, then `g ↦ (f(· g), test)` lies in the joint generalized eigenspace of the
  positive split component `𝔄_J` for the character `b ↦ b^λ`. This combines
  `mem_jointGenEigenspace_of_hasUnnormalizedExponent` and
  `leviPairingLinear_mem_jointGenEigenspace`.
- `leviPairing_finset_sum`: the pairing is additive over finite sums of functions in its
  domain (`integral_finsetSum`).
- `injective_splitComponentCharacter`: the characters `b ↦ b^λ` of `𝔄_J` determine `λ`
  (`eisensteinPositiveParameters`).

## Cusp detection and exponent filtering

- `eq_zero_of_leviPairings_eq_zero` assumes `CuspidalProjectionDecompositionStatement`. Let
  `f` be automorphic on the quotient for `J`, cuspidal along `J`, with absolutely
  convergent pairings, all zero, against every Levi cusp form. Then `f = 0`. Since
  `C_J f = f` (`constantTerm_eq_self_of_automorphicOn`), both `f` and `0` are cuspidal
  projections of `C_J f`, and the uniqueness clause of the statement identifies them.
- `exponentDecomposition_eq_zero_of_tests` takes an exponent decomposition `h = ∑ c λ` of
  a cuspidal automorphic function and a set `Λ` of exponents. Suppose every scalar test of
  `h` is supported, in the sense of `IsJointlySupportedIn`, in the characters of `Λ`. Then
  every component `c λ` with `λ ∉ Λ` vanishes. The test of `h` is the sum of the tests of
  the components, which lie in the eigenspaces of their own characters.
  `fiber_sum_eq_zero_of_isJointlySupportedIn` kills the fibre over `b ↦ b^λ`. Injectivity
  of the characters makes that fibre the single component `c λ`. Cusp detection then gives
  `c λ = 0`. The cusp-detection and integrability inputs are explicit hypotheses.

These are derived consequences of the pairing characterization of cuspidal projections and
the exponent decompositions in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series* (2024), §6.2, (6.8) and (6.10).
