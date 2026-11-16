# Actual rational comparison of different source-chart selections

This internal module constructs `orderSourceQuasi` between two
actual refinements of the same full-order atlas, when their finer
principal covers agree. The two refinements may select different
original charts. The comparison first passes from the first
refined chart to its selected original chart, applies the actual
full-order original transition, and passes into the second
refined chart.

`orderSourceQuasi_eq_onChart` identifies this entire
quasi-isogeny with the chart evaluation of the existing specified
actual `orderSourceIso` between those refinements. Its proof
rationalizes the two integral composition equations defining that
source-choice formal isomorphism. It does not infer equality of
formal maps from their values on points.

The scalar ring is a commutative domain with specified fraction
field, the coefficient ring is any commutative scalar algebra,
the acting order is any algebra ring, and coordinates are finite.
Covers may be infinite. Chart indices are transported by the
specified equality of finer covers, and tests use the
coefficient-ring universe.

The supporting `QuasiIsogeny.trans_symm_trans` cancels the
intermediate actual inverse pair in two pasted rational routes,
using associativity and the stored inverse equations.

The provenance is internal from actual formal source-choice
isomorphisms, refinement chart identifications, full-order
transitions and tensor composition. No framed quotient,
coefficient descent, height statement or representability
assertion is made.
