# Full strong comparison of rational and singleton spectrum atlases

Author: Worker 36.

For every actual presented affinoid algebra, this module constructs full
strong maps in both directions between its rational atlas and its singleton
atlas, and proves both maps are strong quasi-isomorphisms. The ambient maps
are the identity on the original spectrum. The local pullbacks retain
entire bounded algebra maps.

The field `K : Type u` is a complete ultrametric normed field.
`A : PresentedAffinoidAlgebra K` is an actual quotient of a finite
positive-polyradius Tate algebra by a displayed closed ideal. Both spectrum
points and the rational atlas's literal-subset indices occupy universe `u`.
There is no nontrivial-valuation, reducedness, nonzero-quotient,
nonempty-spectrum or nonempty-domain assumption.

`presentation A` bundles the actual `RationalSpectrumAtlas.atlas A` on
`BanachSpectrum A`. `singletonIndexEquiv A` gives an explicit equivalence
from `PUnit.{u+1}` to the published singleton presentation's `PUnit.{1}`
index. Both functions send the unique element to the unique element.
`singletonPresentation A` applies the published presentation reindexing to
this equivalence. Its points, topology, sole algebra `A`, identity chart,
and bounded identity restrictions are unchanged. Both bundled
presentations therefore have universes `u,u,u`, as required by
`StrongHom`; the construction does not identify different index universes.

`toSingleton A` has the continuous identity as its ambient map. At every
rational source index `i` and singleton target index, its pullback is
exactly `i.presentation.baseMap`. The singleton chart has whole spectrum
as its range, so it supplies the target witness. The chart square is
definitional. Simultaneous source and target restriction compatibility is
the already proved equation
`(restriction i i' h).comp i'.presentation.baseMap =
i.presentation.baseMap`, together with the bounded identity law.
`toSingleton_baseMap` and `toSingleton_pullback` expose these exact data.

`toSingleton_chartImageLocus` proves that the source chart's image in the
singleton coordinates is exactly `i.val`: both ambient and target chart
maps are identities, and the rational chart's range is the literal subset
`i.val`. `isQuasiIso_toSingleton` retains the identity homeomorphism and
applies `i.presentation.represents` at every admissible pair. This is the
full representation theorem, including closedness, exact spectrum image
and unique bounded factorization against every presented finite
positive-polyradius affinoid test algebra.

For the reverse direction, `singleton_admissible_locus` shows that any
rational target containing the image of the singleton chart has literal
locus equal to the whole spectrum. This uses containment of the whole
spectrum and subset antisymmetry; it selects no spectrum point.
`fullChartEquiv j h` then applies the published full-domain comparison
between `Domain.whole K A` and the actual represented rational quotient
`j.presentation.toDomain`. Their loci agree by `h` and the representative's
locus equation. Full representation constructs a bounded algebra
equivalence from `A` to `j.presentation.algebra`; an inverse equivalence
is not assumed as input.

`fullChartEquiv_toBoundedAlgHom` identifies its forward bounded map with
`j.presentation.baseMap`, using the comparison's equation over `A` and
the whole-domain identity. `fullChartEquiv_symm_comp_baseMap` and
`baseMap_comp_fullChartEquiv_symm` prove the two bounded inverse equations.
The latter evaluates the algebra equivalence's inverse identity on every
element of the whole rational quotient. These statements retain algebraic
information that need not be detected by spectrum points.

`fromSingleton A` also has continuous identity as its ambient map. The
constructed rational whole chart supplies a target witness, including
when the spectrum is empty. At every admissible singleton/rational pair
it uses the inverse bounded map of `fullChartEquiv`. Its chart square
follows by evaluating the inverse equation over `A` on a seminorm.
For simultaneous restriction compatibility, the source restriction is
the bounded identity. The two competing maps out of the larger rational
quotient agree after composition with its base map: associativity and
`restriction_comp_baseMap` reduce both sides to the bounded identity on
`A`. The published rational universal-property extensionality theorem
therefore identifies the entire bounded maps.
`fromSingleton_baseMap` and `fromSingleton_pullback` record the exact
formulas.

`fromSingleton_chartImageLocus` is the whole target spectrum: the
preimage of the ambient whole spectrum under any target chart is whole.
`isQuasiIso_fromSingleton` uses the identity homeomorphism and transports
the full identity representation along `fullChartEquiv`, by the published
`Represents.precomp_equiv`. This gives full representation for the inverse
bounded map and the preimage of the whole spectrum, which is again whole.
All admissible pairs and all presented positive-polyradius tests remain
in the statement.

The original conventions are V. G. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Definition 1.2.7, printed p.18 /
PDF p.15 (a compatible system at every admissible chart pair), and
Definition 1.2.9, printed p.19 / PDF p.16 (ambient homeomorphism and
affinoid-domain identifications at every admissible pair). The registered
source is `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The full affinoid-test convention is Definition 2.2.1, printed/PDF p.9 of
*Non-archimedean analytic spaces* (Trieste lectures, 2009), source
`berkovich-2009-trieste-analytic-spaces`, SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These original passages were read for the construction; no
source-specific errata file was found in the project lookup.

The two concrete comparisons and their proofs are derived infrastructure
using the published rational quotients, actual atlases, index transport,
full representation and bounded domain comparisons. The sources do not
separately name these constructions. Both strong quasi-isomorphisms are
proved directly. No categorical inverse, general atlas extension or
saturation, unrestricted strong-map composition, localization, analytic
gluing, structure sheaf, étale site or equivariant site is constructed here.
