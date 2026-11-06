# Mixed simple-root semigroups and all-test commutation

Author: Worker 1444.

This internal derived unit uses the actual intrinsic simple roots of a generic
cocharacter and a root datum realizing the ambient roots. It constructs the
literal mixed semigroup of positive multiples of one character plus positive
multiples of the negative of another, using the existing cyclic-tail and
semigroup-sum constructions.

The raw `mixedRootSemigroup` constructor uses two characters of `T`. For the
intrinsic root-exclusion and subgroup-triviality results, `k` is an arbitrary
field, `G` is an affine group scheme locally of finite type over `Spec k`,
`T` is a split torus, and `i : T.toGrp ⟶ G` is the given homomorphism.
The root datum `P` satisfies `IsRootDatumOf i P`, the cocharacter is generic
for the actual roots of `i`, and the two intrinsic simple roots are distinct.
These preceding results do not require ambient smoothness.

For a finite integrally independent family, a positive multiple of one member
minus a positive multiple of another is outside the nonnegative additive monoid.
The proof expresses hypothetical membership by nonnegative coefficients and
uses uniqueness from integral independence: the coefficient of the second
member would have to be negative. Applied to the intrinsic simple-root family,
this excludes both signs of a strict mixed combination from the positive
simple-root monoid.

Every actual root or its negative is positive for the generic cocharacter.
The preceding simple-root monoid-generation theorem therefore excludes every
strict mixed combination from the actual roots. Such a combination is also
nonzero, since zero belongs to the positive monoid. No root-system reducedness
or choice of root/coroot bases is required.

The mixed semigroup consequently contains no ambient tangent weight for the
conjugation action: its characters are nonzero, so occurring conjugation weights
are precisely actual roots. The published semigroup-triviality theorem then
makes its generated subgroup the identity on every scheme test.

For the final commutation theorem, assume in addition that `G` is smooth over
`Spec k`. Under this smoothness assumption, the published first cyclic-tail
comparison identifies the actual
intrinsic root groups with their cyclic semigroup subgroups. The published
all-test semigroup commutator bound, also applied with this smooth affine
ambient group and split torus, places the commutator of the first simple
root group with the opposite of a distinct simple root group in the mixed
subgroup. Its triviality proves `commute_simple_opposite`. The conclusion holds
over every field and on all tests, including nonreduced schemes.

All inputs are imported Library or Mathlib results. This unit proves no graph
density, simple-root algebraic group generation or global projection
invertibility, and supplies no proof of the main isomorphism theorem.
