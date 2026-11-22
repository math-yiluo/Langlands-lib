# Real pair factors of an adjoined character with a shifted exponent

This module collects the bookkeeping identities for real pair `L`- and `ε`-factors needed to
turn the normalized product of a corank-one equation and a matrix equation into the
normalized equal-rank equation for the adjoined block list. It is the real counterpart of
part of the published complex module `ComplexLocalEqualNormalizedFactors`. `charData p z` is
the real character `x ↦ sgn(x)^p |x|^z`. `den(xs, ys)` is the reciprocal pair `L`-factor
`(realPairLFactor xs ys).denominator`, and `ε(xs, ys; b, k)` is `realPairEpsilon xs ys b k hk`.

## Statements

* `realPairLFactor_cons_mul`, `realPairEpsilon_cons_mul`: for a block `d` and lists `ds, es`,
  the pair factors of `d :: ds` against `es` are the products of the singleton factors of `d`
  and the factors of `ds`. `RealLocalEqualJacquetExpansion` uses these identities in its finite-product comparison.
* `realPairBlocks_singleton_character`: against a character list `fs`, the pair blocks of a
  single character `c` are the characters `c · f`, `f ∈ fs`.
* `realPairLFactor_character_shift`, `realPairEpsilon_character_shift`: let two real characters
  `c` and `c'` have the same parity, with `c.exponent = c'.exponent + z`. Then against any
  character list,
  * `den([c], fs)(s) = den([c'], fs)(s + z)`;
  * `ε([c], fs; b, k)(s) = ε([c'], fs; b, k)(s + z)`.

  The specializations `realPairLFactor_charData_shift` and `realPairEpsilon_charData_shift`
  take `c = charData p z` and `c' = charData p 0`.
* `realPairLFactor_equal_pair`: for a block list `ds` and a character list `fs`,
  `den(fs, ds)(s) · den([charData p 0], fs)(s + z) = den(charData p z :: ds, fs)(s)`.
  These are the two denominators of the normalized products in
  `RealLocalEqualFiniteSquareNormalized` and its successors.
* `inverse_charData_eq`, `dualBlock_charData`, `map_dualBlock_character`: the inverse of
  `charData p z` is `charData p (-z)`, and dualizing blocks (`RealLocalJacquet.dualBlock`) of a
  character list inverts each character.
* `determinant_minusOne_sq'`: the value at `-1` of the determinant character of a block list
  squares to one.
* `equal_epsilon_coefficient`: for block lists of ranks `r + 1` and `r + 2`,
  `d(-1)^(r+1) · (det(es, -1)^(r+1) det(ds, -1) · ε(ds, es; a)(s)) · ε([d], es; -a)(s)`
  equals `det(d :: ds, -1)^(r+1) · ε(d :: ds, es; -a)(s)`. Here the first two factors are the
  sign and `ε`-factor of the corank-one equation at parameter `a`, the third is the matrix
  equation at `-a`, and `d(-1)^(r+1)` is the Weyl sign of the dual expansion. The product is the
  equal-rank sign and `ε`-factor of the adjoined list. `RealLocalEqualJacquetExpansion` uses this identity for the equal-rank sign.
* `RealLocalEqualNormalizedFactorsStatement` (proved by `realLocalEqualNormalizedFactors`)
  packages `realPairLFactor_equal_pair` and `realPairEpsilon_charData_shift`.

## Proofs

Against a character list, the pair blocks of `c` are the characters `c · f`. Each has the real
Gamma factor shifted by `exponent + parity`, and the `ε`-factor
`k · (c f)(b) · |b|^(s-1) · i^parity` (`RealCharacterData.coe_epsilon`). Writing the character
values through `character_eq` and combining powers of `|b|` (`Complex.cpow_add`) shows that
raising the exponent by `z` is the same as replacing `s` by `s + z`. The cons lemmas are
`realLFactor_append` and `realEpsilon_append`. The pair identity combines the cons lemma, the
shift and the Library commutation `realPairLFactor_denominator_comm`. The inverse of a
character data structure is determined by its character, parity and exponent. The sign
identity is the published computation: the Library's `pair_epsilon_neg`,
`determinant_realPairBlocks` and `unequal_sign` flip the corank-one `ε`-factor from `a` to `-a`.

## Provenance and scope

These are internal factor identities for Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), §8.2, p. 58, where the product of the two lower-rank functional equations gives the
equal-rank functional equation with `L(s, (χ ⊗ |·|^z) × π) = L(s + z, χ × π)` and the
corresponding `ε`-factors. They say nothing about integrals.
