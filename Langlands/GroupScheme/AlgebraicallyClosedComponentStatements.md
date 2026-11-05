# Rational representatives of components over algebraically closed fields

Author: Worker 1107.

`IdentityComponent.AlgebraicallyClosedComponentComparisonStatement` is an exact
proposition target, with two conjuncts, for the published actual group-scheme
architecture. It is a statement declaration; this module proves neither
conjunct.

For every algebraically closed field `k` in any universe and every actual group
scheme `H` over `Spec k` whose structure morphism is locally of finite type, the
first conjunct asserts surjectivity of `pointComponent H`. Its source is the
group of rational sections `Spec k -> H` over `Spec k`; its target is
`ConnectedComponents H.X.left`, the connected components of the actual scheme's
underlying topological space. The map evaluates a section at the unique point
of `Spec k` and takes its component. Thus every component has a `k`-rational
representative. This conjunct requires neither affineness, smoothness,
connectedness, reducedness nor global finite type. It asserts no finiteness of
the component set at this generality.

For every smooth affine actual group scheme `H` over such a field, the second
conjunct asserts bijectivity of the existing `rationalComponentEmbedding H`.
This is the embedding from the ordinary group quotient `H(k)/H^0(k)` into the
same actual scheme-component set, where `H^0` is the published actual
identity-component group scheme. Its injectivity and the formula relating it
to `pointComponent` are already proved in `IdentityComponentRationalQuotient`.
The retained smooth affine hypotheses are exactly those needed by that
published quotient API. In particular this target does not introduce a second
quotient carrier or an independently assumed component identification.

The provenance is an internal consequence of published constructions and pinned
Mathlib results, rather than a new claim attributed to an external source. The
intended missing proof uses `LocallyOfFiniteType.jacobsonSpace` on the structure
morphism, `isClosed_connectedComponent` and
`nonempty_inter_closedPoints` to choose a closed point in any connected
component. Mathlib's `AlgebraicGeometry.pointOfClosedPoint`,
`pointOfClosedPoint_comp` and `pointOfClosedPoint_apply` in
`Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean` construct a rational section
through that closed point. The formula for `pointComponent` then gives the
first conjunct. For the second, use smoothness to obtain local finite type,
project the representative rational section with
`rationalComponentProjection`, apply
`rationalComponentEmbedding_projection`, and combine surjectivity with the
published embedding's injectivity. These describe a proof obligation, not a
proof supplied by this statement module.

The field is algebraically closed in arbitrary characteristic; there is no
perfection or characteristic-zero restriction in addition to that hypothesis.
The target makes no assertion over a merely separably closed field or a general
base field. It does not assert that fixed geometric components descend to
rational points, identify points of a sheaf quotient with a quotient of points,
construct a component-group scheme, or equip all components with a group law.
The latter can be a subsequent construction after this target is proved, by
transport from the existing rational quotient group.
