# Changing the base of an ordinary marked Harris action

The relative endomorphism ring on each test can be computed using the
direct pullback of the original family or the successive pullback of the
ordinary family on the changed base. The actual Hom comparison
`relativeHomBaseChangeEquiv` is conjugation by the pullback composition
isomorphism, so it also preserves multiplication. This gives the ring
equivalence `relativeEndBaseChangeEquiv`, which is compatible with
restriction of the test.

For an ordinary polarized datum, `Datum.pullbackCompIso` carries the
polarizations and markings on the same two families. The full action
conditions correspond under the endomorphism ring equivalence. The
Rosati comparison uses the actual dual of the same isomorphism. The
determinant comparison rationalizes its intertwining relation and uses
the normalized Lie condition at the common composite map to the CM field.

At each geometric point, marking compatibility is preserved and
reflected by the actual polarized equivariant isomorphism.
`harrisOrdinaryMarkedActionBaseChangeIso` combines these predicates with
the underlying ring equivalence to give the natural comparison on the
locally noetherian test category. Naturality is the ordinary restriction
formula for the same relative endomorphism ring comparison.
