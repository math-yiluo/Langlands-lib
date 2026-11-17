# Local rank-one root support and root-space line statements

`SplitRankOneRootSupportLinesStatement` states the pointwise structural input
needed by the independent split rank-one cell construction. Its field lies in
an arbitrary universe `u`. The group is connected reductive, the supplied torus
is split and maximal, and the supplied root datum `P` satisfies the actual
`IsRootDatumOf` predicate. As in `SplitRankOneRootCellStatement`, every pair of
actual adjoint roots is linearly dependent over the integers.

For each supplied root index `r`, the conclusion is the conjunction of exactly
three assertions: every actual root is `P.root r` or its negative; the actual
weight space at `P.root r` is linearly isomorphic over the field to that field;
and the same is true for the negative character. The weight spaces are the
Library's actual adjoint weight spaces, retaining their defining equations over
every coefficient algebra. `Nonempty` records existence of the two linear
isomorphisms without choosing coordinates. There is no conclusion for an empty
root index type beyond the universally quantified implication.

`AlgClosedRankOneRootSupportLinesStatement` has precisely the same hypotheses
and conclusion, with the additional hypothesis that the field is algebraically
closed. Both declarations are propositions defined with `def`; neither is a
proof. In particular, a supplied Mathlib `RootDatum` does not contain an
`IsReduced` hypothesis, and this module does not infer the support assertion
from the supplied datum alone.

These are internal derived interfaces, isolated by Workers 785 and 777 from the
independent cell construction in Task 7509. Their provenance is the explicit
pointwise support and line-space inputs of that construction, rather than an
additional translation of a literature theorem. They retain the exact field,
torus, root-datum, and rank hypotheses of the published root-cell target,
without adding new assumptions to that target. Their independent geometric
proof remains a separate obligation. The algebraically closed formulation is
a structural prerequisite; it does not replace or restrict the arbitrary-field
root-cell target.
