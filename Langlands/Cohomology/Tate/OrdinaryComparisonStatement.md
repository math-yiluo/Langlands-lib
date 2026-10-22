# Comparison of Tate subgroup maps with ordinary homology and cohomology

Author: Worker 45.

`Langlands.Tate.OrdinaryComparisons` quantifies over a commutative ring, a
finite group and subgroup, a representation, and a positive natural number
`n` (expressed by `[NeZero n]`). It gives four equalities of linear maps:

- Tate restriction in degree `n` is ordinary cohomology restriction transported
  through Mathlib's `isoGroupCohomology`.
- Tate corestriction in degree `n` is `ordinaryCohomologyCorestriction`,
  transported through the same comparisons.
- Tate corestriction in degree `-(n+1)` is Mathlib's covariant homology map
  along subgroup inclusion, transported through `isoGroupHomology`.
- Tate restriction in degree `-(n+1)` is `ordinaryHomologyTransfer`,
  transported through those homology comparisons.

Thus the cohomological range is all positive degrees and the homological
range is all degrees at most `-2`. No comparison is asserted at the norm
splice degrees `-1` and `0`. The ordinary transfers are independently defined
from the standard-resolution coset comparison and relative norm/trace,
not by transporting the Tate maps. These identities are therefore substantive
comparison statements.

Serre VIII §2, printed pp. 129–130 (PDF pp. 135–136), identifies the positive
and negative Tate subgroup maps with their ordinary counterparts. VII §7,
printed pp. 118–119 (PDF pp. 124–125), defines the cohomological corestriction
and homological restriction via their norms and cohomological-functor
extensions. The explicit transport through Mathlib's comparison isomorphisms
and the general commutative coefficient ring are formalization choices.

All objects use Mathlib's actual Tate cohomology and the published operations,
with arbitrary carrier universe `u`. This file declares a proposition; it
contains no proof of that proposition and assumes none of its conclusions.

Source: Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
