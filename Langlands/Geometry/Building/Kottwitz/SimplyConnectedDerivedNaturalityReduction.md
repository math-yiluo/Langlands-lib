# Simply-connected-derived Kottwitz naturality from torus naturality

`SimplyConnectedDerivedKottwitzNaturalAt` states the commuting square for a fixed
actual group-scheme morphism between groups with simply connected derived subgroup.
It supplies a reusable local proposition for the conditional descent argument.

These internal conditional helpers work with actual group schemes and supplied
torus cocenters. They retain five statement assumptions: algebraic
fundamental-group comparison and maps, torus fundamental comparison, fundamental
inertia maps, and torus inertia comparison.

`cocenterTargetMap_natural_of_statements` proves that the map on actual cocenters
commutes with the maps on the reductive inertia targets. The proof composes the
two fundamental inertia maps in each route, uses the actual cocenter quotient
square, and applies conditional naturality of the torus inertia comparison.

`simplyConnectedDerivedKottwitz_natural_of_torus_naturality` also assumes the
simply-connected-derived Kottwitz statement and the torus Kottwitz naturality
square for the particular induced cocenter morphism. Both groups have simply
connected derived subgroup. The target cocenter map is injective by the assumed
statement. Applying it reduces the desired square to the two cocenter Kottwitz
laws, the first helper, and naturality for the induced torus morphism. The actual
quotient square identifies the resulting points.

The result does not prove any of its statement assumptions, torus Kottwitz
naturality, z-extension existence, or the full reductive Kottwitz existence
statement. Its provenance is the formal combination of the named Library
interfaces and the preceding internal helpers; no new literature claim is made.
