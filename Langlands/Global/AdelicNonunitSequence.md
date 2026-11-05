# Explicit adelic nonunit sequences

This construction implements the example in Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), printed p.4, first full
paragraph: nonunits of the adelic ring can converge to 1. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source does not specify the sequence; the following explicit construction
is a derived implementation of that assertion.

For any family of commutative rings with specified subrings,
`integralZeroAtPlace` is the integral tuple with a zero in one position and
ones elsewhere. `restrictedZeroAtPlace` includes it into the original cofinite
restricted product, using Mathlib's `homeoTop` and continuous restricted-product
inclusion. Evaluation at the zero position proves that this element is a
nonunit when the coordinate rings are nontrivial.

For an embedding of the natural numbers into the index set, every fixed
coordinate is eventually 1. Hence these tuples converge to 1 in the product
of integral subrings. Continuity of the actual inclusion proves convergence
in the restricted-product topology, rather than just in the topology induced
by the unrestricted product of the fields.

`numberFieldNonunitPlaceSequence` uses the proved infinitude of the actual
finite places of an arbitrary number field. `numberFieldNonunitSequence`
has all archimedean coordinates equal to 1 and the described integral finite
coordinates. Its noninvertibility and convergence are proved in the existing
full ring `Adeles K` with its original topology.

`curvePlaceNonunitPlaceSequence` uses the proved infinitude of the actual
curve places of a finite extension of `RatFunc k`. The analogous sequence
and its two properties are proved in `CurvePlaceAdeleRing k F`. No separability
hypothesis is added. The construction works over arbitrary constant fields;
when the constant field is finite, this is the actual global function-field
adelic ring already constructed in the Library. The module does not replace
that realization with a supplied abstract family of places.

The general coordinate family and index set have independent universes. The
arithmetic specializations retain their existing common field universe. This
unit constructs and checks the sequences; statements about openness of the
unit locus and maps on actual scheme points are separate consequences.
