# Positive-point lifting through an actual torus product

This internally derived auxiliary unit concerns actual split tori over an
arbitrary number field. `HasPositiveProductFactorization` requires that every
point in the target intrinsic positive subgroup be a product of images of
points in the two specified source intrinsic positive subgroups. It asserts
neither an integral splitting nor lifting of arbitrary rational or adelic
points.

Joint injectivity of the two actual integral character restrictions gives
this positive factorization. For a target positive point, extend its real
logarithmic character functional along the joint restriction into the product
of the source character lattices. Such an extension exists because the
additive group of real numbers is divisible, by Mathlib's proved Baer
extension theorem. Restrict the extended functional to the two factors and
use the published positive-logarithm equivalences of the source split tori.
The two resulting positive points have product with the original target
functional. Their product is still intrinsic positive, and injectivity of
the target positive-logarithm equivalence proves the actual point equality.

If multiplication of the two actual torus maps is an epimorphism of schemes
over the base, a character trivial on both factors is trivial on the target.
This is the published subgroup-product character-detection argument; taking
the kernel gives joint injectivity. If the multiplication is merely supplied
as surjective on schemes, the source factors are finite-type quasi-compact
and the target is smooth, so the published commuting-multiplication theorem
makes it flat. Faithful flatness then gives the required epimorphism.

The proof allows empty splitting index sets and arbitrary kernels. It uses
only the imported positive-logarithm, character-detection, group-scheme
flatness, and additive-homomorphism extension results. No coverage, chamber,
compactness, rational-orbit bound, or norm-one parabolic coordinate theorem
is assumed or concluded. The intended application is the actual derived and
central split-torus product in the Siegel algebraic setup.
