# Compactly supported sections on actual induced rational spectra

This construction specializes the full compact-support locally constant
diagonal module to the actual balanced quotient spectrum of a rational
open-subgroup transport object. It constructs supported functions and maps,
including decomposition into finitely many of the actual rational charts.

## Inputs and scope

The inputs are a complete ultrametric normed field `K : Type u`, a presented
strict affinoid algebra `P` over `K`, a topological group `G : Type v`, and
an actual `RationalSpectralAction G P`. For
`X : ρ.OpenSubgroupTransport`, write `H` for its stored open subgroup.
The space `X.LocalSpectrum` is the Banach spectrum of its rational quotient
algebra. The induced space `X.InducedSpectrum` is the constructed balanced
quotient `G ×_H X.LocalSpectrum`, in universe `max u v`, with its topology
and continuous full-group action.

The coefficient ring `R : Type r` is any commutative ring. Coefficient modules
`V : Type w` are arbitrary `R`-modules without topology. The four universes
`u`, `v`, `r` and `w` are independent. The resulting function carrier has
universe `max u v w`. No finiteness of `G/H`, group separation, nonemptiness,
or nontriviality of the coefficient module is imposed.

## Actual support and smooth action

`CompactSections.Functions` is the full submodule of locally constant
`V`-valued functions on the induced spectrum whose topological support is
compact. Topological support is the closure of the nonzero locus. Local
constancy makes the zero fiber open, so that nonzero locus is already closed;
`tsupport_eq_support` records the equality.

`componentSupport` is the image of the actual nonzero locus under
`X.inducedComponent : X.InducedSpectrum → G/H`. The compact-chart criterion
from `InducedRationalCompactCharts`, applied to this closed locus, proves
`hasCompactSupport_iff_finite_componentSupport`. Thus compact support is
equivalent to finiteness of these actual nonzero coset components.
`finite_componentSupport` and `exists_finite_chart_cover` expose the two
consequences for supported functions. Finiteness is proved from the function,
rather than supplied as extra structure.

For `M : SmoothRep R G`, `smoothRepresentation X M` retains every supported
locally constant function and the diagonal formula
`(g • f)(z) = M.representation g (f(g⁻¹ • z))`. Its smoothness is the generic
compact-support theorem: an open spatial stabilizer, together with the
finitely many coefficient stabilizers for the function's range, fixes the
whole function. `coefficientFunctor` maps all smooth coefficient modules
and intertwiners; its map is the actual pointwise coefficient map
`f(z) ↦ b(f(z))`.

## Chart extension and finite reconstruction

`chartExtension` uses `Function.extend` along the subtype inclusion of the
actual compact clopen chart `X.inducedChartDomain a`, with zero outside.
Compactness of the chart gives compact support. The open chart inclusion,
Mathlib's continuous extension by zero, and a temporary discrete topology on
the coefficient module prove local constancy. This temporary topology adds no
input condition on the coefficients.

The evaluation lemmas prove equality with the original chart function on the
chart and vanishing outside it. `tsupport_chartExtension_subset` places its
support inside that chart. `chartExtensionLinear` and
`chartRestrictionLinear` are the actual linear extension and restriction
maps, and `chartRestriction_extension` proves that restriction after
extension is the identity. `localChartExtension` first transports a locally
constant function on `X.LocalSpectrum` through the inverse of
`X.inducedChartHomeomorph a`, then extends it by zero. Its evaluation at
`X.inducedChart a x` is exactly the original value at `x`.

`chartPart a` is restriction followed by extension. It is idempotent. For
distinct cosets `c` and `d`, the projections for the chosen representatives
`c.out` and `d.out` are orthogonal. The formula `chartPart_out_apply` says
that the `c`-projection evaluates to `f(z)` precisely when the actual
component of `z` is `c`, and otherwise to zero.

`sum_chartPart_eq` reconstructs `f` from any finite coset set containing
`componentSupport X f`. Evaluation reduces the sum to its unique component;
outside the supplied finite set the support containment forces `f(z) = 0`.
`exists_sum_chartPart` chooses the finite set proved above. Coefficient
intertwiners commute with chart extension, as proved by
`coefficientMap_chartExtension`. A single-chart extension is a linear map;
no full-group equivariance of that one chart is asserted.

## Proper transport

For an actual transport arrow `f : X ⟶ Y`,
`Hom.compactSupportPullback` is ordinary precomposition along
`f.inducedMap`, under the explicit hypothesis
`IsProperMap f.inducedMap`. Properness and continuity preserve compact
support; the constructed equivariance of `inducedMap` makes this a morphism
of smooth representations. The evaluation formula is
`s(z) ↦ s(f.inducedMap z)`.

Identity induced maps are proved proper, and proper induced maps are closed
under transport composition using the existing induced-map identity and
composition laws. The pullbacks obey the corresponding contravariant
identity and composition laws. `compactSupportPullback_naturality` proves
commutation with all smooth coefficient maps. This makes no properness
claim for a general transport arrow between varying subgroups.

## Provenance and remaining constructions

This is internal derived mathematics from the actual induced rational
spectrum and its compact-chart criterion, the full compact-support smooth
module, and the pinned Mathlib support and extension APIs. The support
criterion, chart projections and reconstruction are elementary consequences
of those constructed objects; no new assertion from Harris or Berkovich is
claimed here.

The functions are not identified with analytic etale sheaf sections or
derived cohomology. Supported cochain complexes, analytic and etale
comparisons, arithmetic coefficient systems, the Harris tower realization,
and its cohomological compatibility theorems remain separate obligations.
