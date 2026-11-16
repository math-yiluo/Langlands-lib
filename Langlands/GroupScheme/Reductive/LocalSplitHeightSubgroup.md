# Root-height subgroups on every scheme test

Author: Worker 204.

This construction applies the derived abstract height filtration to
actual root maps over a commutative ring. A root factor is the image of
its additive global-function parametrization on a test scheme.
Precomposition preserves these factors and their generated height
subgroups, producing the all-test subgroup functor `heightSubgroup`.

Under the open big-cell and torus-equivariance hypotheses, a cocharacter
strictly negative on the negative factors and strictly positive on the
positive factors gives positive integer heights. The universal
commutator identity of `LocalSplitHeightCommutator` is evaluated on each
test scheme. Its convention is converted to the standard group
commutator by swapping the inputs and negating both root coordinates.
The resulting commutator lies in the subgroup at the sum of the input
heights.

The abstract collection theorem now supplies ordered coordinates for
every height point, with coordinates below the level equal to zero.
Conversely such supported coordinates lie in the height subgroup. The
open cell makes the ordered coordinates unique on every test scheme.
The abstract normalization theorem shows that each next level is normal
in the current one, and each level is normal in the subgroup generated
by all the listed positive roots.

These are derived supporting results for Conrad, *Reductive group
schemes* (2014), Theorem 5.4.3, pp.174–177. The cocharacter hypotheses are
explicit, and this unit does not construct a filtration for an arbitrary
parabolic, represent these subgroups, or descend their quotients.
