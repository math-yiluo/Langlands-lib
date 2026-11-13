# Special formal division-order modules in local coordinates

This derived unit imposes the special tangent condition on actual formal
division-order atlases and the height d² condition on their actual chart
scalar kernels.

## Source and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), permits formal groups glued over localizations just before
section 2. Section 2 A defines special formal O_D-modules by their dimension
d and their distinct geometric tangent characters, then uses height d² for
the framing module and objects of his functor. The registered original is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
This module combines those conditions with `SpecialModule`, `BasicAtlas`
and the constructed atlas order actions. The comparisons and preservation
results are internal consequences of that infrastructure.

The parameters are a nonarchimedean local field K, a finite-dimensional central
division K-algebra D and a supplied K-embedding of a field L into D.
Set d = `CentralSimple.reducedDegree K D`. The division order and embedded
integer subring are the actual restricted-valuation rings of `DivisionOrder`
and `SpecialModule`. The unramified-subfield condition is the existing
finite-dimensionality, finite etale integer algebra and full-degree predicate.
Existence of that subfield and specialization to Hasse invariant 1/d remain
open obligations.

Each atlas has one fixed coordinate type `Fin d` on a supplied principal-open
cover. Tests have the base ring's universe v, families v+1, and the geometric
character condition uses algebraically closed fields in `max u v` as in
`SpecialModule`. Morphisms and isomorphisms here compare equal generator sets.
No refinement invariance, general change of base for atlases, independence
of the chosen unramified subfield, comparison with all formal schemes, framing
object, full Drinfeld functor or representability is asserted.

## Original charts and inverse maps

`BasicAtlas.coefficientRingLift` exposes the ring map underlying the chart
coefficient extension. `coefficientLift_self` identifies this map from a
localization to its own chart with the identity by the localization universal
property.

`isoOfIdentityCoefficient` recovers an isomorphism between two original formal
module laws from an isomorphism after coefficient extension whose underlying
ring map is the identity. The source and target O-algebra structures on that
ring may have different presentations. The identity ring map and its scalar
compatibility force these algebra structures to agree. After transport along
that equality, the two `mapIdIso` comparisons give the original isomorphism.

`BasicAtlas.OrderAction.Iso.onChart` evaluates both actual inverse formal atlas
maps on a test algebra. Their formal inverse equations specialize to the
inverse equations for actual order-linear chart maps. `originalChartIso`
then gives an actual O-linear
isomorphism between the original chart laws over their localization rings,
using `isoOfIdentityCoefficient` and `coefficientLift_self`.
This is sufficient for scalar-kernel height transport.

## Special atlases and actual heights

`SpecialAtlas K D iota R` consists of an actual `BasicAtlas` in dimension d,
an actual action of `IntegerRing K D` commuting with its formal transitions,
the specified unramified-subfield condition, and the existing geometric
distinct-character condition on each original chart's differentiated action.
`chartModule` recovers the actual `SpecialModule` over R[1/b].
`chartTestModule` extends it to any coefficient test on which b is a unit;
the existing coefficient theorem preserves the geometric characters.

`HasHeightSquared pi` requires irreducibility of pi in O_K, nilpotence of
its actual image in R, and `HasPiHeight pi q (d^2)` on every original chart,
where q is the actual residue-field cardinality of K. The chart condition
includes affine fppf scalar lifting, pi-power torsion, finite projective
representing algebras for all scalar-power kernels, and their actual stalk
ranks q^(n*d²). The global nilpotence condition is explicit. No local-to-global
equivalence with an abstract p-divisible sheaf is used.

`base_nilpotent`, `chart_height` and `chartTest_height` expose these
consequences. The last uses actual scalar-kernel base change.
`Iso.hasHeightSquared` transports chart heights along `originalChartIso`;
the irreducibility and global base condition are unchanged. Applying this
in both directions gives `Iso.hasHeightSquared_iff`. `HeightSquaredAtlas`
is the subtype carrying this height property.

## Actual points and restriction of global modules

`Point`, `pointFunctor` and `nilpPointFunctor` reuse the division-order modules
of actual compatible nilpotent families. `chartPointEquiv` is the constructed
division-order-linear equivalence with the actual special chart module wherever
the chart is defined. `Hom` and `Iso` are the existing actual same-cover
division-order-linear formal atlas maps and their formal inverse pairs.

`ofGlobalCover` restricts the formal law and order action of a global
`SpecialModule` to any supplied principal-open cover. The special tangent
characters restrict by the geometric coefficient theorem.
`ofGlobalCover_height` restricts every scalar-kernel height certificate.
`ofGlobal` specializes to the singleton cover.
`globalPointEquiv`, `globalPointFunctorIso` and `globalNilpPointFunctorIso`
are the already constructed division-order-linear singleton comparison,
its natural isomorphism after universe lifting, and its restriction to Nilp.
