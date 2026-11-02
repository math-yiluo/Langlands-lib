# Open-chart and functoriality properties of actual scheme point topologies

This unit states the open-chart and continuity assertions needed to glue the
already constructed affine evaluation topologies on actual relative scheme
points. The named `schemePointTopology` is the explicit final topology from
all actual affine open charts; the conclusions are not fields of an assumed
topology package.

## Source and derived scope

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 3.1 and proof, printed page 4. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proposition treats locally finite type schemes over a local topological
ring with open units and continuous inversion. Its proof establishes the
affine-open assertion by basic-open localization and local-ring coverage, then
uses gluing for arbitrary schemes in its scope.

The statements here are the derived relative formulation of the open-chart
and continuity portion. `R` and `S` are commutative rings in a common arbitrary
universe, `S` has its specified `R`-algebra structure, and only `S` is topologized.
The hypotheses are `IsLocalRing S`, `ContinuousMul S` and `IsOpenUnits S`.
The last says that units, with their existing value-and-inverse topology, map
as an open embedding into `S`; it incorporates openness and the subspace
inversion condition. It is a separate premise from localness.

These particular claims extend to arbitrary schemes without a finite-type
hypothesis and require only continuous multiplication rather than all ring
operations. Localization fractions give inverse-continuity using multiplication
and the unit topology; arbitrary coordinate-pullback maps are continuous for
evaluation topologies, and local-ring coverage requires no finiteness. These
facts justify the stronger derived scope of this part. They do not extend
finite-type-dependent local compactness claims to arbitrary schemes.

## Exact targets

All declarations lie in `Langlands.AlgebraicGeometry.PointTopology`.

- `AffineOpenPointProperty R S` says that for every affine relative scheme `X`
  and every affine open `U` in `X.left`, the actual postcomposition map
  `openPointMap R X S U` is an open embedding. Both spaces carry the already
  constructed affine evaluation topology.
- `SchemeOpenPointProperty R S` says that for every relative scheme `X` and
  every open `U`, the same actual inclusion is an open embedding when both
  source and target carry their explicitly named `schemePointTopology`.
- `SchemePointContinuityProperty R S` says that actual postcomposition with
  every morphism of relative schemes is continuous between those final point
  topologies. It quantifies over actual morphisms in `Over (Spec R)`.
- `SchemeOpenPointProperties R S` is the conjunction of these three assertions.

Every point space is the existing actual `RingPoint` carrier. `openOver`
retains the actual open subscheme and its structure map to the same base, so
the source and target of the inclusion have the specified relative meaning.
No alternate topology or unspecified chart equivalence appears in the targets.
The affine comparison itself is already a proved intrinsic property of the
imported final-topology construction.

This contribution supplies statement targets. It proves none of these three
assertions and does not assert the remaining uniqueness, fiber-product,
closed-immersion, Hausdorff, or locally compact conclusions of Proposition 3.1.
Those and all later-paper obligations remain with the parent task.
