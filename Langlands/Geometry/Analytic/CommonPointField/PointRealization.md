# Compatible realization of one analytic point

Internal derived construction for the common analytic point field.
For an affinoid atlas presentation `A` and a point `x`, this module constructs a
complete ultrametric normed `K`-algebra field `PointField.Carrier A x` and a
`FieldPoint` over it with underlying point `x`.

Containing charts form a directed preorder under reverse inclusion: the atlas
net supplies a smaller chart containing the point inside any two such charts.
The point has a unique spectrum representative in each containing chart because
chart maps are embeddings. Their completed residue fields form a directed
system under the canonical isometric maps induced by bounded restrictions.
Uniqueness of continuous maps out of a completed residue field proves identity
and composition of those maps. The paired supporting module
`Spectrum.ResidueField.Functorial` implements that uniqueness using fractions
in the kernel quotient and their dense image in its completion.

The isometric direct limit carries the representative norm, and its metric
completion is the point field. Each chart evaluation is the canonical completed
residue map followed by the component embedding. The norm formula follows
from the two isometric inclusions and the residue-map norm formula. The
direct-limit transition relation proves compatibility with every atlas
restriction. The field universe is the maximum of the coefficient and chart
index universes, independently of the space universe. This module does not
construct a single field for different underlying points or assert algebraic
closedness.

The provenance is derived from the published atlas, actual completed residue
fields and their canonical maps, together with Mathlib's algebraic direct limit
and metric completion. It introduces no geometric point axiom.
