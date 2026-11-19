# Naturality of Serre's Brauer comparison

For a field extension `E/K`, let `S/K` and `T/E` be separable closures
with a compatible embedding of `S` into `T` over `K`. Embed the finite
splitting stage for an actual central simple K-algebra in `T`. A finite
Galois subextension over `E` contains this image. The scalar extension
of the original matrix chart splits the scalar-extended algebra over
this finite Galois field. Its relative class is given by ordinary
inflation followed by ordinary restriction. The continuous cohomology
square identifies this class after inflation with actual cohomological
restriction, using the induced Krull group map and inclusion of units.
This is `brauerContinuousEquiv_scalarExtension` on the actual Brauer
quotients.

The Brauer comparison is surjective, so naturality makes any two
compatible closure embeddings induce the same map on degree-two
cohomology. When the base field stays fixed, the comparison identifies
the degree-two groups for two choices of separable closure. That
identification equals the map of any compatible embedding and composes
under a third closure choice. It also commutes with restriction when both
the source and the target closure are changed. For Mathlib's chosen separable closures,
`separableRestriction` uses a separable-field embedding, with independence
of that choice given by the same theorem.

This is the scalar-extension naturality of the descent/PGL comparison in
J.-P. Serre, *Local Fields* (1979), Chapter X, §5, printed pp. 158–159. The
proof computes Serre's scalar factor set transported through the
matrix chart and applies in every characteristic.
