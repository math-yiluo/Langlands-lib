# Local kernel-rank heights on rational atlas maps

This internal construction applies the existing
`RationalSection.HasHeightFunction` relation to actual chart evaluations of a
global rational formal atlas map. It provides a rank-based zero-height condition
for later framing data; it does not assign an arbitrary height to a map.

Let O be a commutative ring, R a commutative O-algebra, and F a field that is an
O-algebra. R and F have the same universe. The coordinate types are finite and
may differ. The source and target atlases have equal specified principal covers;
the covers may be infinite. Test algebras have R's universe.

`BasicAtlas.RationalHom.HasConstantChartHeight f π q n` requires, for every
R-algebra test A and every target chart whose generator becomes invertible in
A, that the sheaf section of the actual rational coordinate evaluation of f
has the constant height function n. Each height presentation uses an actual
integral formal map representing a power of π times that section. Its numerator
and source scalar-power kernels have actual finite locally free representations
and constant ranks q^a and q^b, with n = a − b. The numerator is also an actual
isogeny with the existing affine fppf lifting condition. The neighbourhood,
denominator exponent, numerator and rank exponents may vary with the point.
No global common denominator for these local presentations is required.

The condition is imposed on every test chart, not just one selected
localization. `isLocallyScalarIsogeny` extracts the existing local
scalar-isogeny relation. `restrict` retains the constant rank difference on any
open subset of the test chart. Given nonvanishing of π in F and actual
π-divisibility of both evaluated coordinate laws, `localQuasiIsogeny` constructs
the existing genuine local quasi-isogeny. Its section is exactly the image of
the evaluated rational atlas map.

The auxiliary `RationalSection.HasHeightFunction.ofIntegralIso` proves that an
actual integral isomorphism has rank difference zero on an open set. It uses
exponent zero: both the numerator isomorphism and multiplication by π^0 have
kernel rank one and isogeny height zero. `ofGlobalIso` applies this construction
after actual coefficient extension to the global section algebra.
`BasicAtlas.OrderAction.Iso.hasConstantChartHeight_zero` applies this proof to
every evaluated actual full-order chart isomorphism. It therefore proves the
height-zero condition for the rationalization of an integral full-order atlas
isomorphism, for any specified π and q.

The provenance is entirely internal: rational chart evaluation and full-order
formal isomorphisms come from `AtlasRationalMorphism`, `AtlasOrderRationalMorphism`
and `SpecialAtlas`; the local height relation comes from `RationalHeight`; actual
isomorphism kernel ranks come from `KernelTransport`. The proof uses these
constructions directly and makes no new assertion attributed to original
literature.

The rational map here belongs to the global tensor of integral atlas maps.
This module does not assert that such maps exhaust all locally rational maps.
Existence, uniqueness and denominator independence of rational heights,
additivity, invariance under arbitrary atlas refinements, coefficient-base
change of this condition, framed isomorphism classes and representability
remain separate obligations.
