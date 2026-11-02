# Standard cocharacters from independent rationalized simple roots

Worker 185. This is an internal lattice construction on the published
`Rational.StandardParabolic`, `Torus.Lattice`, `Torus.LatticeGalois` and
`LinearAlgebra.RationalSpan` interfaces. Its root-independence hypothesis is
explicit. It does not prove the general reductive root-system theorem or the
three dynamic-subgroup comparisons in `StandardCocharacterStatement`.

A rational functional on a finite split-torus character lattice can be realized
by an integral cocharacter after multiplication by a positive integer.
`IsSplitTorus.exists_positive_multiple_pairing` first transports characters and
cocharacters along a splitting isomorphism. In split coordinates their pairing
is the dot product. It evaluates the functional on coordinate vectors and
clears their finitely many denominators using Mathlib's localization lemma.
Squaring the resulting nonzero integer gives a positive common multiplier;
multiplying the integral coordinate numerators once more by that integer
preserves the required equality. This also covers a rank-zero torus.

`IsSplitTorus.exists_scaled_pairings` starts with an independent family of
rationalized actual characters and any prescribed integer values. The family
is a basis of its span. The prescribed values define a rational functional on
that span, which Mathlib's `Subspace.dualLift` extends to the full rationalized
character lattice. The preceding result realizes a positive integral multiple
of its values by a cocharacter. No finiteness of the index type is imposed.

`exists_standardCocharacter_of_linearIndependent` applies this result to the
actual simple relative roots, with value zero on `J` and one on its complement.
It assumes splitness of the actual torus, independence over the rationals of
these rationalized roots, and the actual subset containment for `J`. It needs
only an affine ambient group to form the published relative roots. It assumes
no reducedness, field characteristic, root-system theorem, or dynamic-subgroup
comparison. Empty root sets and both endpoint subsets are included.

`standardCocharacterOfIndependentRoots` chooses the resulting cocharacter;
its specification theorem proves the published `IsStandardCocharacter`
predicate. This is a conditional helper for the general theorem. Discharging
independence from connected reductivity and maximal splitness, and proving the
dynamic comparisons, remain separate obligations.
