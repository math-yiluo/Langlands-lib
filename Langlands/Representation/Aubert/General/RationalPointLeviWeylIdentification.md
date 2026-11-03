# Pairing stabilizers and actual standard Levi Weyl images

Worker 165. This internal conditional construction isolates the quotient and
descent part of identifying actual Levi Weyl groups with standard Coxeter
subgroups. It retains the original point Coxeter system and literal simple-root
labels. The simple-reflection pairing law defined below remains unproved.

Work over any field, with a commutative group scheme `T`, an affine group scheme
`G`, and a monomorphic map `i : T → G`. Both actual normalizer and full-centralizer
comparisons `hN` and `hZ` are explicit. There is no local-field topology or
representation-theoretic input.

`pointCocharacterPairingWeylStabilizer` is the subgroup of the actual quotient
`Weyl i` that preserves pairing with a fixed cocharacter on every character.
`pointNormalizer_mem_dynamicCentralizer_iff_pairing` proves, for split `T`, that
membership of a specific point normalizer representative in the dynamic
centralizer is equivalent to its class being in this stabilizer. The proof
uses the representative formula for `weylCharacterAction`,
`normalizerPoint_mem_dynamicCentralizer_iff`, compatibility of the character and
cocharacter actions with the lattice pairing, and perfectness of the split-torus
pairing. The same ambient normalizer point is used throughout.

`mem_pointStandardWeyl_iff_pairing` then characterizes the image of the actual
Levi Weyl inclusion: it is exactly the classes preserving pairing with every
standard cocharacter for that face. In one direction use a representative in
the choice-free standard Levi. In the other direction choose any representative
of the given quotient class and apply the preceding equivalence to each standard
cocharacter. Thus no extra equality of subgroup families is assumed.

`SimpleReflectionPairingInvariance` is an explicit remaining proposition. For
each actual simple root `a`, it says that the point Coxeter generator `cs.simple a`
preserves pairing with every cocharacter annihilated by `a`, on the whole
character lattice. This module does not derive that assertion from
`RootLengthComparison` or `PositiveSimpleReflectionComparison`.

`standardSubgroup_le_pointPairingStabilizer_of_simplePairing` extends this law
from the simple generators of a face to their subgroup closure.
`pointPairingStabilizer_eq_standardSubgroup_of_simplePairing` proves the reverse
inclusion by induction on Coxeter length. A right descent sends its simple root
to a negative root, by the supplied `RootLengthComparison`. The relative-root
system and splitness supply the opposite root, while genericity makes its pairing
strictly positive. Nonnegative pairing of positive roots with a standard
cocharacter forces this descent label into the face. The simple-reflection law
then preserves the stabilizer while reducing length. This argument follows the
published descent route in `CoxeterCocharacterStabilizer`, using the original
point action without assuming `IsRelativeWeylCoxeterRealization`.

`actualLeviWeylIdentification_of_simplePairing` combines the stabilizer equality
and the actual quotient characterization. Existence of a standard cocharacter
is derived from `HasRelativeRootSystem.exists_standardCocharacter`. Its output
is exactly the range of the published actual Levi Weyl inclusion being
`standardSubgroup cs I` for every finite face `I`. It needs the split torus,
relative-root-system, genericity and length/sign hypotheses and the explicit
unproved simple-reflection pairing law. It does not require a finite root set,
finite Weyl group, reductivity, a scheme Coxeter realization, or an arbitrary
choice of normalizer representatives.

The provenance is derived Library mathematics: the actual quotient and action
in `RationalLeviWeylComparison` and `RationalWeylRootAction`, the dynamic
centralizer criterion in `CocharacterCentralizer`, split-torus perfectness in
`Absolute.RegularPerturbation`, positive-root pairing induction, relative-root
negation and standard-cocharacter existence, and Mathlib's Coxeter descent
theorems. No classification, character independence, geometric lemma,
adjointness, cuspidal-support result or normalized-functor comparison is used.
This conditional unit supplies neither the remaining simple-reflection law nor
an unconditional proof of `RationalJacquetCompatibilityStatement`.
