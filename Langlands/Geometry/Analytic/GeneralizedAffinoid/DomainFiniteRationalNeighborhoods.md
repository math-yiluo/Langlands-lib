# Finite ambient rational covers from finite-union neighborhoods

Author: Worker 84.

This internal construction extends `DomainRationalNeighborhoodCover` to
neighborhoods that are finite unions of ambient rational chart loci. It is
intended for a scalar-descent argument in which a rational chart over an
extension field pulls back to several rational charts over the original field.
No scalar-descent theorem or local-neighborhood existence is assumed proved.

`FiniteRationalNeighborhood U x` consists of a natural number `size`, ambient
charts indexed by `Fin size`, and actual arrows from their full represented
domains to `U`. The preimage of the union of their loci under the inclusion
`U.locus → BanachSpectrum A` must belong to the neighborhood filter of `x`.
This condition applies to the union. No individual member is required to be a
neighborhood of `x`. `single` converts a previously constructed single rational
neighborhood to a family of size one.

`ofPreimage` accepts a continuous map out of `U.locus`, a neighborhood of its
value at `x`, and an equality expressing that neighborhood's preimage as a
finite union of contained ambient rational charts. Continuity proves the
relative-neighborhood condition; the specified charts and actual arrows are
retained.

`FiniteRationalCover.ofFiniteNeighborhoods` chooses one finite family at each
point of `U.locus`. The existing compactness of the represented locus gives
finitely many of those relative neighborhoods covering `U.locus`. The
constructor enumerates the finite dependent sum of their chart indices by a
`Fin` type. Its coverage proof first selects a covering neighborhood, then a
member of that neighborhood's union, and uses the enumeration equivalence.
Every arrow is copied from the chosen local family, preserving the bounded
algebra restriction and its structural compatibility. Empty domains require
no additional hypothesis; the compactness and dependent-sum construction also
allow empty index families.

`finiteRationalCoverStatement_of_finiteNeighborhoods` applies this constructor
to local finite-union neighborhoods for every field, ambient presentation,
full represented domain and point at the full universe `u`. It is a conditional
reduction of the published target. Establishing those local neighborhoods for
all domains remains an analytic obligation.

The compactness assembly is an internal adaptation of the finite-cover step
of M. Temkin, *A new proof of the Gerritzen–Grauert theorem* (2005), registered
source `temkin-2005-gerritzen-grauert`, PDF SHA256
`1948a0be381d7dd4d4b5166c9b00f2ffa903a30a6ee0ffd09f754a5e9ad9c334`,
printed/PDF p. 5, first paragraph of the proof of Theorem 1.1, and p. 8,
Theorem 3.1. The finite-union packaging and continuous-preimage adapter are
internal derived constructions and are not asserted as separately numbered
results of that source.
