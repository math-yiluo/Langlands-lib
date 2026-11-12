# Gamma factors of highly ramified twists against unramified principal series

Module `Langlands.Representation.RankinSelberg.HighlyRamified.UnitaryGamma`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It is a step toward the
essential-vector input `EssentialPairInput` (module `HighlyRamified.EssentialInput`) for
p-adic fields. That input is needed for highly ramified twists, whose L-factor is trivial.
The module computes the gamma factor of a highly ramified twist `τ ⊗ η ∘ det` of rank
`n + 3` against every unramified principal series of rank `n + 2`.

## Provenance

The computation is the one used in Jacquet, Piatetski-Shapiro and Shalika 1981, *Conducteur
des représentations du groupe linéaire*, proof of Theorem (5.1)(ii). There the functional
equation is applied against the unramified representations of the smaller group. The route
here is internal to this project. It uses the following Library results:

- the uniform rank-one statement, through `exists_bound_rankOne_gammaMonomial` (module
  `HighlyRamified.RankOneMonomial`);
- the unramified twist of gamma factors `unramifiedTwistGamma`;
- gamma multiplicativity `gammaMultiplicativity` (JPSS 1983, Theorem (3.1)(i)).

## Results

- `exists_spectralShiftUnit_eq`: for `q > 1` every `z ∈ ℂ^×` equals `q^(-u)` for some
  complex `u`. Take `u = -log z / log q`.
- `prod_rationalEpsilonMonomial_coe`: a finite product of epsilon monomials `c_i X^(e_i)`
  is the epsilon monomial `(∏ c_i) X^(∑ e_i)`. The proof is induction on the finite set,
  using `rationalEpsilonMonomial_mul_coe`.
- `twist_rankOneCharacter_one`: twisting the trivial rank-one test `rankOneCharacter 1` by
  `χ ∘ det` gives `rankOneCharacter χ`. Both act on `ℂ` by `χ(det g)`.
- `isPadicSymmetricGammaFactor_unramifiedTest`: suppose `c X^e` is a gamma factor of
  `(π, rankOneCharacter 1)`. Let `μ_z = T.unramifiedCharacter z` be the unramified character
  with `μ_z(ϖ) = z`. Then `c z^e X^e` is a gamma factor of `(π, rankOneCharacter μ_z)`.
- `exists_bound_principalSeriesGamma`: fix the rank `n` and a level `f`. There is `B` such
  that the following holds for every generic `τ` of `GL_(n+3)(F)` with a nonzero vector
  fixed by `1 + ϖ^f M(O)`, and every quasicharacter `η` with `a(η) ≥ B`. Put
  `e = (n + 3) a(η)`. There is `c ∈ ℂ^×` such that for every `z ∈ (ℂ^×)^(n+2)`,

  `c^(n+2) (∏ z_i)^e X^((n+2) e)`

  is a gamma factor of `(τ ⊗ η ∘ det, principalSeriesOfTuple F z)`. Here
  `principalSeriesOfTuple F z` is the normalized principal series of the unramified
  characters `μ_(z_i)`. The constant `c` depends on `τ` and `η` but not on `z`.

## Proofs

`isPadicSymmetricGammaFactor_unramifiedTest`. Choose `u` with `q^(-u) = z`. The unramified
character `χ` with value `q^(-u)` at the uniformizer satisfies `χ(x) = |x|^u`; this is the
argument of `symmetricGammaFactor_determinantComplexPower_of_transport` in module
`AdjacentRankFixedGamma`. The first clause of `unramifiedTwistGamma` gives the gamma factor
`R(q^(-u) X)` of `(π, (rankOneCharacter 1) ⊗ χ ∘ det)`, where `R = c X^e`. Rewrite the test
with `twist_rankOneCharacter_one` and `χ = μ_z`. The rescaled monomial is `c z^e X^e`.

`exists_bound_principalSeriesGamma`. Take `B` from `exists_bound_rankOne_gammaMonomial` at
rank `n + 3` and level `f`. Let `π' = τ ⊗ η ∘ det`; it is of Whittaker type because it is
generic.

1. A gamma factor of `(π', rankOneCharacter 1)` exists: apply `gammaMultiplicativity` with
   one block. By the choice of `B` it equals `c X^e` for some `c`.
2. Fix `z`. Apply `gammaMultiplicativity` to `π'` and the `n + 2` blocks
   `rankOneCharacter μ_(z_i)`. Each block is of Whittaker type
   (`rankOneCharacter_isOfWhittakerType`). This gives gamma factors `G_i` of the blocks.
   Their product is a gamma factor of `π'` against the normalized product of the blocks. That
   product is, by definition, `principalSeriesOfTuple F z`: the block shape with all sizes
   `0 + 1` is the Borel shape, and the blocks are the characters `μ_(z_i) ∘ det` of `GL_1`.
3. Gamma factors are unique (`IsPadicSymmetricGammaFactor.unique`). By the previous lemma,
   `G_i = c z_i^e X^e`.
4. Multiply: `∏_i c z_i^e X^e = c^(n+2) (∏ z_i)^e X^((n+2) e)`. This uses
   `prod_rationalEpsilonMonomial_coe` below.
