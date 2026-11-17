# Chart covers for multiplicative-type subgroups

Author: Worker 872.

`MultiplicativeTypeSubgroupModuli.ChartCoverStatement.{u}` asks for a
family of actual smooth open subgroup charts for each smooth affine
group scheme over every base scheme. The charts must cover the
actual closed multiplicative-type subgroups over every field-valued
point, with parameter points over the same field.

`FiniteTypeChartCoverStatement.{u}` asks for this conclusion only when
the base is the spectrum of a ring of finite type over `ℤ`.
`ChartCoverReductionStatement` is the implication from this
finite-type form to the arbitrary-base form. `ChartGluingStatement`
is the implication from the arbitrary-base chart cover to the
smooth universal-family proposition. These are proposition definitions;
this module proves no chart-existence or gluing theorem.

These are internal intermediate statements for the smooth moduli
theorem of SGA 3, Exposé XI, Theorem 4.1 (registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF pp.20–21,
recomposed pp.104–105, original pp.157–159). They generalize the
published torus chart statements by allowing all relative groups of
multiplicative type, including torsion character groups and nonsplit
forms. No Noetherian hypothesis is imposed in the arbitrary-base
statement and no connectedness condition is imposed on the ambient
group. The finite-type form concerns the actual subgroup chart
predicate; it is not a finite-type condition on the parameter scheme.

The companion `MultiplicativeTypeChartLifting` module proves that the
arbitrary-base chart-cover proposition alone implies the unchanged
étale lifting target. This is a conditional theorem: chart existence
remains an explicit hypothesis. In particular the lifting application
does not require the global moduli-gluing implication.
