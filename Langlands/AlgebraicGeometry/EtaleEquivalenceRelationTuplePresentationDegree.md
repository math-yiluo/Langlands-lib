# Degree and off-diagonal maps in total tuple presentations

This derived module connects the actual finite tuple presentation to the
exact-degree and off-diagonal constructions. Its mathematical provenance is
the symmetric tuple stratification in Stacks Project, Lemma 68.8.3, Tag 0BBN,
and its finite version, Lemma 68.8.6, Tag 07ST. These are registered as
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. The module uses the implemented
scheme constructions and their proved properties; it assumes no quotient or
Noetherian approximation result.

The original relation has affine object and arrow schemes, separated source,
and closed joint endpoint map. Schemes have arbitrary universe `u`. The
chart family is indexed by a finite type. A chart of length `n` parametrizes
unordered distinct related tuples with `n+1` entries.

`tupleChartDegreeι` includes the exact-degree scheme of a chart into the
total object scheme. It is a closed immersion, being a composite of closed
immersions. `tupleChartDegreeUnit` includes its unit arrows into the total
relation. The two endpoint formulas identify both composites with the degree
inclusion. The exclusion lemma states that this inclusion avoids the next
total threshold.

Suppose a chart is strictly shorter than every other chart in the family.
`tupleChartObjectι_index_eq_of_not_threshold` shows that any component point
outside the next threshold belongs to that shortest chart: all longer
charts lie entirely in the threshold. `tupleChartDegree_factors_unit` proves
that every arrow whose source factors through its exact-degree scheme is
the corresponding unit. Threshold invariance first excludes both endpoints
from the next threshold. The preceding component lemma then places the
arrow's image in the shortest chart's self-correspondence. Its open inclusion
supplies a factorization on the entire test scheme. The implemented unit-locus
theorem forces that factorization to be a unit, and the source equation
identifies its base point. This argument applies to arbitrary, including
nonreduced, test schemes.

`tupleChartDegree_unit_isPullback` gives the resulting scheme-theoretic
source pullback. Its universal property follows directly from the
factorization theorem, with uniqueness supplied by the identity projection
to the degree scheme. `tupleTailLowestIndex` names the shortest index in a
nonempty finite tail, the strictness lemma verifies that every other index
is longer, and `tupleTailDegree_unit_isPullback` specializes the cartesian
square to that tail.

`tupleChartOffDiagonalLeft` and `tupleChartOffDiagonalRight` factor the
endpoints of a chart's nonidentity self-correspondences through the next
total threshold. The component threshold formulas and the proved
off-diagonal containment put the endpoints in that open; the open immersion
universal property supplies the maps. Their inclusion formulas recover the
original endpoints in the total object scheme. The two swap formulas state
that the existing off-diagonal involution exchanges these factored maps;
they follow by cancelling the total open inclusion.

These declarations supply degree and off-diagonal adapters for the total
presentation, together with an actual cartesian square over its lowest
exact degree. They do not construct a Noetherian first level.
