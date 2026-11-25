# The torus quotient law in actual rank-one centralizers

This internal module applies the all-test rank-one torus-quotient theorem
from `RankOneCellQuotient` to actual reductive groups over commutative local
rings. It uses the published actual relative centralizer, pointed etale
unit-cell and affine Weyl-data constructions. It assumes no reducedness,
noetherian, henselian or characteristic restriction.

`LocalSplitCell.RankOneQuotientLaw i xm xp q` is a proposition about the
actual indicated maps from a coordinate split torus and two additive
groups into `G`, and the torus map `q` into `Q`. On every relative scheme
test it says that an equality
`(xm(y) * i(t) * xp(x)) * xm(z) = xm(y') * i(t') * xp(x')`
implies `q(t) = q(t')`. All five scalar parameters are arbitrary global
functions on the test, and the torus points are arbitrary. This property
does not itself assume root parametrizations, reductivity or any geometric
condition.

`RankOneQuotientLaw.of_faithfulBaseChange` proves that the property descends
along every scalar extension whose pullback on relative schemes is
faithful. Its hypothesis uses the actual base changes of the two root
maps and torus maps, expressed in standard additive and split-torus
coordinates. The proof pulls an arbitrary relation back, uses the
coordinate-preserving point equivalences to apply the supplied law,
and detects equality of the pulled-back torus images by faithfulness.
`cocharPoint_trivial_baseChange` separately shows that a torus map killing
a fixed-exponent cocharacter on all points retains that property after
any scalar extension, in the same standard coordinates.

For the actual-group theorem, the base ring is local, `G` has affine
structure morphism and is reductive, `i` is a closed split torus maximal
on every field fibre, and `P` is a fibrewise root datum for `i`. The
finite coordinate type has decidable equality. The maps `xp` and `xm`
are supplied actual parametrizations of the roots `a` and `-a`. The
target `Q` has affine structure morphism. The explicit hypothesis on
`q` is that it kills the actual coroot of `a` on every relative scheme
test.

`RelativeCocharacterCentralizer.rankOneQuotientLaw` first retains a
supplied integral cocharacter `mu` whose vanishing roots consist only
of `a` and `-a`. The actual coroot centralizer has an open rank-one cell
with the given lifted root parametrizations. Over the closed point of
the local base, `pointedEtaleUnitCellReflection` and its affine
restriction give the prescribed normalizer and unit cell coordinates.
The affine coefficient ring therefore carries the actual
`affineEtaleWeylData`, with exactly the original root coordinates and
the actual coroot. Its projection is etale and surjective on the entire
local spectrum, so pullback is faithful. The base-changed torus map
kills this coroot by the preceding transport lemma. The all-test
rank-one quotient theorem applies to these Weyl data, and faithful
descent gives the quotient law in the original centralizer.

`LocalSplitCell.rankOneQuotientLaw_of_reductive` chooses a suitable
`mu` using the published kernel-exponent construction. Its finiteness
and reduced-root-datum inputs follow from the supplied fibrewise root
datum. Since the centralizer inclusion is a closed immersion, it is
monic; any relation between the original three-factor rank-one points
is therefore also a relation between their actual centralizer lifts.
The centralizer law proves the advertised `RankOneQuotientLaw` in `G`.

`rankOneQuotientLaw_corootProjection` specializes the result to the
all-coroot torus quotient `RelativeDerived.corootProjection`. The
fibrewise root datum identifies the integral pairing with the coordinate
dot product, and `corootProjection_coroot_points` proves the required
actual annihilation. Thus no extra torus-killing premise remains in
this specialization. All relative scheme tests, including nonreduced
tests, remain quantified.

The property defined here and the accompanying theorems concern actual
rank-one relations. Extraction from a full cell relation, construction
of the ambient quotient, and the full relative derived-group existence
theorem remain further steps.
