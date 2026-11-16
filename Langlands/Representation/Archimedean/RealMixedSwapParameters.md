# Parameters for signed reversal of mixed real blocks

This internal helper for Task 7171 defines the parameters needed when the signed
rank-three reversal is applied to a real induction block and a character block.
It uses the existing Library character constructions, with no classification or
irreducibility assumption.

For a complex character datum `d` and a real character datum `b`, put
`q = |d.weight| + 1`. The definitions in namespace
`Langlands.Archimedean.RealMixedSwapTwist` are:

- `unitSign x = x/|x|`, viewed in the complex numbers for a real unit `x`;
- `reverseInduced d = characterOfParams d.weight (-d.exponent)`;
- `signedInverseCharacter q b`, with parity `(q + b.parity.val) mod 2`
  and exponent `-b.exponent`;
- `mixedSignPower d = q` and `reverseCharacter d b = signedInverseCharacter q b`.

The elementary sign lemmas prove that `unitSign x` squares to one and is unchanged
by inversion. `abs_inv_cpow` applies the complex-power identity for the inverse of
a positive real number. These identities give `signedInverseCharacter_apply`:

`(signedInverseCharacter q b).character x = unitSign x ^ q * b.character (x⁻¹)`.

For the induction block, inverse reversal exchanges its two position characters.
Multiplying both by `unitSign x ^ q` places the sign power on the first character,
matching the Library convention. The two lemmas
`realInducedFirstCharacter_reverse` and `realInducedSecondCharacter_reverse`
prove these identities directly from the definitions and the sign-square lemma.
Their exponent equalities are ring computations. The lemmas
`positionCharacter_induced_character` and
`positionCharacter_character_induced` assemble the three coordinate identities
for the two possible orders of the mixed pair. They quantify over `j : Fin 3`
and use `Fin.rev j` for the corresponding original coordinate.

`exponent_order_reverse` proves that the order required for the reversed
character-induction pair is equivalent to the order for the original
induction-character pair. It simplifies the real parts of the negated exponents.
For nonzero `d.weight`, `unlinked_reverse` proves the equivalent mixed
unlinkedness conditions. Both blocks have singleton Mœglin data; the mixed
linkedness formula ignores the character parity and is symmetric in the two
exponent differences. Negating both exponents exchanges those differences.

This module supplies parameter computations only. It does not construct an
intertwiner or prove the mixed swap. Provenance is internal and derived from the
published Library definitions in `StandardModule`,
`RealLargeStandardIrreducibleReduction`, `RealStandardIrreducibleCriterionReduction`,
`RealJacquetFrobeniusProof`, and `ComplexJacquetBorel`. The signed-reversal strategy
and division of work were developed with Worker 767.
