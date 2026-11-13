# Coordinate atlases and actual glued nilpotent points

This is a derived construction of formal O-module point functors with varying
local coordinates on a principal-open cover of an affine base. It implements
actual formal transition maps and their compatible nilpotent tuple families.
The local chart equivalence is proved from those equations. No representing
formal scheme, universal module or uniformization is supplied as input.

## Original source and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), the paragraph immediately
before section 2 on printed p.109 (PDF page 3), enlarges formal groups to objects
glued from formal groups over localizations of the base. The source is registered
as `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The constructions here are an explicit functor-of-points implementation of that
local-coordinate convention, rather than a transcription of an additional
numbered theorem in the source.

The base is a commutative O-algebra R, and the finite coordinate type σ has a
fixed cardinality. The charts are indexed by a subset s of R satisfying
`Ideal.span s = top`, the usual principal-open covering condition. Each chart a
is an actual `ModuleLaw O (Localization.Away a.val) σ`: its pointed power series,
formal addition, inverse and natural tangent O-action come from the previously
defined coordinate module laws. Chart and test coefficient rings lie in the
same universe v. The point module lies in universe v+1, since its families range
over all `CommAlgCat.{v} R` test algebras and their algebra maps.

This unit treats natural formal transition families over every common test
algebra. It does not yet derive such families from a single map over each
explicit pair-localization, identify refinements of presentations, construct
a formal scheme or prove a general comparison with formal schemes or Cartier
modules. The construction keeps constant finite dimension on the chosen base.
Order actions, special-module conditions, isogeny heights, framing and the
Drinfeld/Rapoport–Zink moduli functors remain additional work.

## Localization and actual formal transitions

`BasicAtlas.coefficientLift` is the localization universal map R[1/a] → A,
regarded as an O-algebra map, for an R-algebra A in which a is a unit.
`coefficientLift_algebraMap` identifies its restriction to R, and
`coefficientLift_comp` proves its compatibility with every R-algebra map A → B
by the uniqueness part of the localization universal property.

`coefficientTriangleIso` identifies the law obtained by successive coefficient
extension with the directly extended law. Its underlying formal coordinate map
is the identity; equality of the addition and scalar-action series follows from
coefficient composition and the localization-map equation. `pointMap` is the
resulting O-linear map on chart points. Its underlying function applies the
coefficient map to the nilpotent series tuple. `pointMap_id` and `pointMap_comp`
prove its two functor laws. `unit_map` transports the actual unit condition.

`ModuleLaw.BasicAtlas` consists of the cover, the chart laws, and actual
`ModuleLaw.Iso` transitions from chart a to chart b whenever both are defined
over a test algebra. Each isomorphism includes formal forward and inverse maps
and their two inverse equations. The structure requires identity transitions,
the composition cocycle, and equality of the mapped forward coordinate series
under every coefficient map. Naturality of the inverse follows from the
isomorphism equations; the structure does not substitute arbitrary bijections
of point sets for formal maps.

`ChartPoint` is the actual chart law's `Point Empty`. The existing
`SeriesPoint.nilpotentEquiv` identifies these underlying points with tuples of
nilpotent elements of the test algebra. Their O-module operations are those
of the formal law. `transitionPoints` evaluates the formal isomorphism to an
O-linear equivalence of these tuples. Its identity, cocycle and coefficient
naturality equations are proved from the corresponding formal equations.

## The constructed functor

A `ChartTest A` consists of an R-algebra B, an R-algebra map A → B, a chart a,
and a proof that a is a unit in B. A `Family A` assigns an actual point in that
chart over B to every such test. `Compatible` imposes both equations:

- Coefficient extension along B → C sends the B tuple to the tuple at the
  composite test A → C.
- At a common test algebra, the evaluated formal transition sends the a tuple
  to the b tuple.

All maps in these equations are O-linear. `compatibleSubmodule` constructs their
simultaneous solution submodule of the product of actual chart-point modules;
`Point A` is that submodule. Zero, addition and scalar closure are proved with
the linear map laws. No abstract point functor is taken as extra data.

`evaluation` is the O-linear map selecting the tuple at a test. `mapPoints`
extends an atlas point along A → A' by precomposing each test A' → B. Its
compatibility proof uses the original family's equations and associativity of
algebra maps. Its identity and composition equations are proved as equalities
of families. These define the actual functor `pointFunctor` from commutative
R-algebras to O-modules. `nilpPointFunctor π` restricts it through the full
category of R-algebras in which the image of π is nilpotent.

## Local chart equivalence and proof

For any chart a which is a unit in A, `ofChart a ha` constructs a compatible
family from a nilpotent tuple x in that chart. At a test A → B in chart b,
it first extends x to B, then applies the actual a-to-b transition. Its
coefficient compatibility follows from transition naturality and composition
of `pointMap`. Its chart compatibility is exactly the transition cocycle.

`chartEquiv a ha` is an O-linear equivalence between `Point A` and the actual
chart's nilpotent tuples. The forward map evaluates at the identity test A → A
in chart a, and the inverse is `ofChart`. One inverse equation uses the
identity coefficient map and identity transition. For the other, the family's
coefficient compatibility determines its a tuple at each test from its tuple
at A; chart compatibility then determines the tuple in every other chart.
Thus the constructed point functor is locally the specified formal module on
every chosen chart. This result does not by itself supply a formal-scheme
representability or a comparison for all possible atlas presentations.
