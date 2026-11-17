# Assembly of split Borel structure with an affine vector-quotient series

Author: Worker 591. The represented root-height terms, successive quotients
and endpoint identifications are supplied by Worker 204's general
`RelativeUnipotent.RootHeightChart` construction.

This internal assembly works in every universe over every commutative ring,
including the zero ring. It derives an affine vector-quotient series directly
from a supplied positive root-height chart, then connects the specific split
Borel positive chart to `HasSplitBorelVectorSeries`.

`HasAffineVectorSeries.of_iso` transports a supplied series across an actual
group-scheme isomorphism without changing its length. The length-zero
terminal clause agrees definitionally with the vector-bundle-series clause,
so the existing transport theorem proves that case. At positive length, the
closed kernel inclusion is composed with the isomorphism, and the quotient
is precomposed with its inverse. Closedness and the fppf quotient's geometry
and exact all-test kernel are preserved; the quotient vector group and
recursive kernel series stay the supplied ones.

`RootHeightChart.hasAffineVectorSeries_of_bound` takes a bound n with every
root height below n+1. A finite induction through represented terms at
positive heights constructs the recursive `HasAffineVectorSeries`. Each
step uses the actual next-term closed inclusion and the represented fppf
quotient to the standard polynomial vector group of exact-height rank.
The standard coordinate multiplicative equivalences and their naturality
on all scheme tests prove the required `IsVectorGroup` predicate directly.
This uses the specific free vector quotients, rather than assuming every
vector-bundle additive group is globally free.

Above the supplied height bound the represented term is trivial on every
scheme test by `range_id_eq_bot`. Starting at height one and using
`heightOneIso` therefore gives a series of length n on the original group.
`hasFiniteAffineVectorSeries` chooses the finite maximum height as n, with
zero for an empty root family. Empty layers yield allowed rank-zero vector
quotients; no connectedness of a total space is used.

`hasSplitBorelVectorSeries_of_positiveChart` takes a reductive group, a
closed fibrewise maximal coordinate split torus, its actual common
fibrewise root datum, an actual positive chart, and an affine-vector series
on that chart's contracting group. It applies
`AffineRegularBorel.hasSplitBorelVectorSeries_of_contractingSeries`, using
the chart's regularity. This supplies the actual relative Borel, its closed
affine kernel, the split torus projection and represented fppf quotient
with the all-test kernel identity.

`hasSplitBorelVectorSeries_of_rootParametrizations_and_chartSeries`
constructs the positive chart from supplied actual root parametrizations,
then applies that assembly to a supplied series construction for these
charts. Its two premises are constructed in the exact final proof module;
this conditional helper alone does not prove their existence.

The provenance is internal composition of the stated Library interfaces.
The specific scheme chart is never treated as a group-scheme isomorphism
or used to replace the contracting group law by addition.
