# Compact support from bounded Cartan coordinates in a quotient

This is internal support machinery for the forward implication of Renard
VI.2.1. It is derived directly from finite integral boxes and compact products;
it introduces no structural existence assertion about reductive groups.

`CartanDetectionModulo pair e` says that equal root coordinates imply equal
images under `e`. Its finite-image theorem takes a finite root index type and
bounds every coordinate between two integers. The box of coordinate tuples is
finite. Each tuple has at most one image, so the image of all bounded parameters
is finite. Neither injectivity of the parameter map nor finiteness of its fibers
is assumed. The empty root index type is allowed.

`hasCompactSupport_of_bounded_cartan_image` takes a continuous surjective group
homomorphism `q : G →* Q`, where `Q` is a Hausdorff topological group, a compact
set `K` in `G`, and a finite residual set `F₀`. If each nonzero value at `q g`
has an expression `g = k₁ f e(x) k₂` with outside factors in `K` and uniformly
bounded integral root coordinates, and the coordinates determine `q (e x)`,
then the function on `Q` has compact support. The support lies in the product
of the compact image of `K`, the finite product of residual and parameter
images, and the compact image of `K`. Mathlib's compact support criterion
then includes the closure of the support because `Q` is Hausdorff.

All five type universes are independent. No topology on the function's target,
continuity of the function, or topology on the parameter type is required.
This helper alone does not prove the geometric or Jacquet-module inputs of
Renard VI.2.1.
