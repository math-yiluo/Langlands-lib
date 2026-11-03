# The actual tangent image of coordinate weight subgroups

This internal unit computes the actual Lie image of the coordinate weight
subgroup in the original affine group over an arbitrary field and at every
universe `u`. The input is an actual automorphic action of a commutative group
scheme, a chosen isomorphism with a split torus on a finite index type, and an
arbitrary additive semigroup in the original character lattice. No condition
on zero or nonemptiness of the semigroup is imposed.

`infinitesimalCoordinate f` evaluates the existing identity derivation on the
original coordinate function `f`. It is a linear functional on the original
`Additive (lieKernel G k)`, and its value is the second component of the actual
dual-number point coordinate. The original all-algebra action weight condition
agrees with `Corepresented.IsWeightTangent` under the chosen character
identification. The comparison uses naturality to identify constant torus
points and the character evaluation formula, preserving the character sign.
The existing corepresented tangent calculation therefore makes every pure
weight vector vanish on all coordinate components of different weights.

On an affine test, the corepresented affine point equivalence recovers the
original point after the inverse coordinate model isomorphism. The relative
global-sections comparison transports this identity to the all-test range
criterion. Coordinate weight-subgroup membership is preserved and reflected
by the global-sections/algebra isomorphism, using the cut-out ideal's
naturality. This proves `mem_range_weightHom_affine` without finite type or
smoothness assumptions.

For an actual tangent vector, reduction to the identity fixes the constant
component of every coordinate to its augmentation. Membership in the quotient
subgroup is thus equivalent to vanishing of the coordinate derivatives in
all excluded degrees. Consequently every included ambient character weight
space lies in the tangent image. Conversely a pure excluded weight vector in
the image is zero: the membership condition kills its coordinate derivatives
in that degree, and its weight condition kills the derivatives in every
other degree. The original affine coordinate equivalence then identifies it
with the identity tangent vector.

For `tangentSubmodule_range_weightHom_eq` and
`hasLieImage_range_weightHom`, assume additionally that the ambient group is
locally of finite type. The closed quotient inclusion gives an affine source
locally of finite type. Its all-test stability allows the existing represented
stable-subgroup theorem to decompose its tangent image as the sum of the
intersections with ambient weight spaces. Included intersections lie in the
semigroup span, and excluded intersections are zero by the preceding result.
The reverse inclusion is the pure included-weight calculation. This proves
that the tangent submodule is exactly `RelativeRoot.semigroupWeightSpan b A`,
and equivalently the published `RelativeRoot.HasLieImage` predicate.

The provenance is internal composition of the actual identity derivation,
coordinate weight-tangent calculation, relative affine point comparison,
coordinate quotient construction and stable represented weight decomposition.
The supporting `TorusCoordinateWeights` and `TorusActualWeightSubgroup` pairs
are unchanged work of Worker 1281. The present unit does not identify the
quotient with the generated semigroup functor or assert connectedness,
maximality, uniqueness, unipotence, split unipotence, or the full
`SemigroupRealizationStatement`.
