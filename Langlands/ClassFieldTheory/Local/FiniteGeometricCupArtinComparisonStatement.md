# Character comparison for geometric inverse cup

This internal proposition formulates an alternative to
`FiniteCupArtinCharacterComparison`, using the actual
`geometricReciprocityOfCup` in place of arithmetic inverse cup. It does not
assert that either comparison has been proved, or identify which sign is correct.
The original comparison and common-closure target are unchanged.

`FiniteGeometricCupArtinCharacterComparison` quantifies every prime, every p-adic
field `F` in the stated arbitrary universe, every finite Galois extension `D/F`
in that universe, every positive fundamental class for the exact canonical
relative invariant `FiniteArtinSymbol.relInv F D`, every certificate that its
degree-minus-two cup is bijective, every character of the actual Galois group
into `Multiplicative (ZMod [D:F])`, and every base-field unit. It asserts that
evaluating geometric inverse cup on that unit's actual determinant-norm class,
through the character's lift to the actual Galois abelianization, gives the
published positive carry value `FiniteArtinSymbol.symbolValue`. No abelian
Galois-group assumption is made. Geometric inverse cup is the inverse of
arithmetic inverse cup in that abelianization, as defined in `TateAbelianization`.

The provenance is internal: this is an explicit comparison between existing
constructions, with their complete telescopes and canonical invariant retained.
`FiniteGeometricCupArtinComparison` gives the conditional finite transfer
consequences. This proposition supplies no proof of the comparison, the cyclic
sign calculation, or unconditional common-closure reciprocity existence.
