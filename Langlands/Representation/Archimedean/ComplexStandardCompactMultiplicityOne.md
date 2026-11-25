# A compact multiplicity-one vector in complex standard modules

`Langlands.Archimedean.complexStandardExistsCompactScalarVector` supplies a
nonzero vector in the `U(n)`-finite complex standard module of any list of `n`
characters. Every `ℂ`-linear endomorphism commuting with the `U(n)` action sends
this vector to a scalar multiple of itself.

For a list in nondecreasing order of weights, `exists_minorWeight_eq` expresses
these weights as those of a product of bottom-row minors and an integral
determinant power. The character comparison `positionCharacter_untwist`
allows `ComplexMinorProduct.mulV` to multiply this minor monomial by the
normalized spherical vector of the weight-zero list. That spherical vector
is constant one on `U(n)`, so the product restricts to the minor monomial.
The restriction is nonzero at the reversing permutation matrix, by
`minorMonomial_revUnitary_ne_zero`. The scalar conclusion is
`complexLowestKTypeMultOne`.

For any list, `Tuple.sort` sorts the positions by weight. `permKMap` for the
sorting permutation and its inverse gives injective compact intertwiners in
both directions. `surjective_of_injective_of_kMap` makes the map from the
sorted module to the original module a linear equivalence. Conjugating a
compact endomorphism by this equivalence reduces its action on the transported
vector to the sorted case.

This is an internal lemma for the proof of
`CuspidalArchimedeanStandardIrreducibleStatement`. The sorted construction uses the
minor weights and untwisting from `ComplexTemperedStandardIrreducibleProof`,
and the spherical vector from `ComplexSphericalLieGroup`. The compact
multiplicity-one calculation and permutation transport are the published
constructions in `ComplexLowestKTypeMultOne`, `ComplexPermutationKMap` and
`ComplexPermutationKType`.
