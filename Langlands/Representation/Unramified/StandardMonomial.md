# Standard monomials in the spherical Hecke algebra (internal interface)

Internal interface module for the proof of `SphericalHeckeGenerationStatement` (Gross 1998,
Prop. 2.6 and (2.7)–(2.9), triangularity of products of the standard elements with
respect to the dominance order). The support half of the triangularity is proved
in `StandardMonomialSupport`, the nonvanishing of the top coefficient in
`StandardMonomialTop`, and the generation assembly from triangularity in
`SphericalHeckeGenerationProof`. This module fixes only the shared definitions
and the interface proposition.

## Definitions

- `standardUniformizer F`: the unit `F.canonicalTopologicalData.uniformizerUnit`
  used by `standardDiagonal`.
- `standardTorus F ν`: the torus element `diag(ϖ ^ ν 0, …, ϖ ^ ν r)`, i.e.
  `GeneralLinear.Iwasawa.torus (standardUniformizer F) ν`.
- `torusHeckeElement F ν`: the corner double-coset element of `K ϖ^ν K`.
- `monomialExponent a` for `a : Fin (r + 2) → ℕ`: entry `j` is `∑_{i > j} a i`.
  Then `ϖ^{monomialExponent a} = ∏_i standardDiagonal i ^ a i`, and the exponent
  is antitone with nonnegative entries.
- `standardMonomial F a`: the product `T_0 ^ a 0 ⋯ T_n ^ a n` (`List.ofFn`
  product; the corner is commutative by the published Gelfand theorem, but the
  type carries no commutative instance).

## Interface

`StandardMonomialTriangularity F` states, for every `r` and `a`:

1. if `standardMonomial F a x ≠ 0`, then `x ∈ K ϖ^ν K` for some antitone `ν` with
   `tailSum λ k ≤ tailSum ν k` for every `k` and `∑ ν = ∑ λ`, where
   `λ = monomialExponent a` (`ν` is dominated by `λ`);
2. `standardMonomial F a (ϖ^λ) ≠ 0`.

Proofs. `StandardMonomialSupport` proves clause 1. It bounds the minors and the
determinant valuation of the elements in the support, using the published bounds
`minor_mul_left_le` and `minor_mul_right_le` and the tail-sum comparison on torus
elements. `StandardMonomialTop` proves clause 2 and combines both clauses into
`standardMonomialTriangularity`. Convolutions of nonnegative spherical functions
are nonnegative, and they are strictly positive at a product of points where the
factors are positive: the integrand is continuous and nonnegative, and Haar measure
gives open sets positive mass. Neither proof uses a Cauchy–Binet formula or a
quantitative lower bound on convolutions.
