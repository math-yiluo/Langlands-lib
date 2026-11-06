# Zariski locality of represented subgroup membership

Author: Worker 1726.

This module proves that membership in the range of a monomorphic actual
group-scheme homomorphism is local on any open cover of a test scheme. It
then proves that containment in such a subgroup, and equality of two such
subgroups, can be checked after base change to any open cover of the base.
The base and test schemes are arbitrary `Scheme.{u}`; the cover can be
indexed in any universe `v`. There is no quasi-compactness, affineness,
reducedness or finiteness assumption. Closed immersions are examples of
the monomorphisms to which these results apply.

`coverObj` and `coverMap` regard each member of a test scheme's open cover
as an object over the original base, with its actual relative inclusion.
The theorem `mem_range_iff_openCover` takes local factorizations through
the subgroup. Monicity makes the factorizations agree on every overlap.
Mathlib's `Scheme.Cover.glueMorphisms` glues their underlying scheme maps.
The structure-map equality and the factorization through the inclusion
are verified on the same cover. The resulting actual relative map
witnesses membership in the original range.

For `le_range_iff_baseChange_openCover`, pull the base cover back to an
arbitrary test scheme. The actual pullback point equivalence translates
the assumed local containment to local membership of the original point.
The preceding theorem then descends that membership.
`range_eq_iff_baseChange_openCover` applies the containment criterion in
both directions. `eq_iff_isRepresentedBy_baseChange_openCover` rewrites
using the two supplied all-test representatives.

These are internal descent lemmas for the construction of torus-subgroup
moduli. Their provenance is the ordinary gluing property of morphisms of
schemes and uniqueness of factorization through a monomorphism, implemented
using Mathlib's scheme gluing API. They construct no moduli scheme and do
not yet glue a family of varying subgroup schemes.
