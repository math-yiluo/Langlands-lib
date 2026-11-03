# Integral coroot extraction from character differences

This is derived algebra for the geometric relative-root reflection construction.
It does not assert that the required geometric normalizer exists. The original
reflection-existence target is in `Rational.RootReflectionExistenceStatement`.

For a torsion-free integral module `M`, a nonzero element `a`, and a linear
endomorphism `w`, suppose every difference `x - w x` is an integral multiple of
`a`. `IntegralCoroot.differenceFunctional` uses the inverse of Mathlib's linear
equivalence from the integers onto the span of `a` to define the coefficient as
one integral linear functional on all of `M`. `differenceFunctional_smul` proves
its defining factorization. If `w a = -a`, cancellation along the nonzero vector
shows that the functional takes value two at `a`. The full action formula then
follows by subtraction.

For the actual character lattice of a split torus,
`IsSplitTorus.existsUnique_coroot_of_integral_difference` transports that
functional through the existing integral perfect lattice pairing. It obtains
one actual cocharacter with self-pairing two and the reflection identity for
every character. Uniqueness follows by cancelling multiples of the nonzero
root and then using injectivity of the perfect pairing in its cocharacter
argument. Torsion-freeness of the character lattice follows from the
reflexivity induced by the perfect pairing.

The difference hypothesis is integral, not merely a rational-line condition;
no primitivity or indivisibility is required of `a`. There is no characteristic,
perfectness, root-system, finiteness, or connected-reductive premise. The result
applies to any nonzero character and endomorphism satisfying the two stated
algebraic laws; it supplies no intrinsic normalizer or full-kernel centralizer
existence theorem. All assertions here are internal consequences of the
existing lattice pairing and Mathlib's linear algebra, rather than a new
translation of a literature theorem.
