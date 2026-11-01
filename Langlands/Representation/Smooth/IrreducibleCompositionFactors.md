# Smooth composition-factor sums and exact descent

This module constructs the canonical finite sum of irreducible smooth
isomorphism classes of a finite-length smooth representation, and its
integer-linear descent from the exact Grothendieck group. The field, group,
and representation carrier have independent universe levels `uR`, `uG`,
and `uV`. The group has an arbitrary topological space structure. There
is no admissibility, finite-dimensionality, resizing, or
topological-group compatibility premise.

`gradedSmooth` equips each actual graded representation of an object filtration
with inherited smoothness, using subrepresentation smoothness and surjective
transfer along the actual quotient projection. The carrier universe is fixed.
`seriesClass` sums the genuine irreducible labels of a supplied composition
series. Its coordinate formula is the existing factor multiplicity cast from
the naturals to the integers. The published generic Jordan–Hölder independence
and equivariant transport results identify the sums for different series and
for isomorphic objects.

`chosenSeries` selects an actual finite composition series from finite
group-algebra length, using the published `exists_series` result.
`compositionFactors` is its finite factor sum and agrees with every supplied
composition series. `compositionMultiplicity` retains the natural count and
its actual Jordan–Hölder witness. Coordinate multiplicity additivity for
actual short exact sequences proves additivity of the whole finite sum.

`oneStep_graded_equiv` identifies the one-step quotient with the original
representation via an actual surjective quotient map. Consequently the factor
sum of an irreducible object is its single genuine irreducible generator.

`classFactors` descends through actual smooth isomorphism classes. Its exact
additivity allows `factorMap` to descend through the defining relations of the
existing exact finite-length Grothendieck group, using its published universal
property. Its computation on every actual finite-length object is proved.
The provenance is internal algebra: actual smooth objects, their group-algebra
composition series, the genuine labels of `IrreducibleRealization`, and the
exact quotient of `FiniteLengthGrothendieck`, which imposes relations from
all actual short exact sequences, including nonsplit sequences. The proofs
use generic Jordan–Hölder independence, equivariant transport, existence,
uniqueness, and short exact additivity supplied by
`Filtration.MultiplicityAdditivityProof` and its imports. No numbered
literature assertion is transcribed. This module uses no parabolic,
analytic, Aubert, or classification input, and asserts no bijectivity of
the realization map.
