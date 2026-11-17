# Root support and coroots in normal subgroup functors

Worker 634.

This internally derived helper uses actual root subgroup functors of a supplied
split maximal torus of a connected reductive group over a field. It defines the
root support of an arbitrary subgroup functor and proves that normality makes it
stable under every realizing root-datum reflection. A normal subgroup functor
containing a root group contains the corresponding actual coroot on every
scheme test. Any root group centralizing that normal subgroup therefore has zero
Cartan pairing with every supported root.

The coroot containment uses the published monomorphic rank-one parametrizations
and Gauss relation. For an arbitrary unit u, choose X=1 and Y=u-1. Solve the Gauss
relation for the middle coroot factor; the other four factors lie in the two
opposite root groups. Normality supplies the opposite root through the actual
normalizer reflection. The final orthogonality follows from the published
centralizer tangent-weight formula and the nonzero actual root weight space.

These are internal consequences of the imported root functor, rank-one and
weight-space results. They prepare the component almost-simplicity argument in
the local-product route motivated by Conrad, *Reductive group schemes* (2014),
Proposition 6.4.4, pp.232–233. No almost-simplicity or component-product existence
is asserted here.
