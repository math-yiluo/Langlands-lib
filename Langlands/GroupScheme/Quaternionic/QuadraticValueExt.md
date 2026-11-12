# Detecting quadratic forms by vector values

This internal derived module proves that the vector values of a quotient-valued
quadratic form determine its element of the published matrix quotient.
The proof applies to every division algebra with an involution of the first kind
and every characteristic.

The alternating subspace is proper: if it were the whole algebra, the involution
would negate every element, forcing characteristic two and hence making every
alternating difference zero. A nonzero element cannot multiply the whole
division algebra into this proper subspace. Polarization of a form whose values
all vanish therefore forces every polar matrix entry to vanish.

A matrix lies in the quadratic kernel precisely when it is skew-hermitian and
its diagonal entries are alternating. The reverse direction explicitly chooses
alternating-difference representatives on the diagonal and uses the upper
triangle for the remaining entries. A zero-valued form has these two properties,
so its matrix class vanishes. Apply this result to the difference of two forms
to obtain extensionality.

The module uses the square specialization of the rectangular matrix pullback
in [QuadraticPullback](QuadraticPullback.md). That construction descends
congruence to the actual quotient and proves its row-evaluation formula.
The identities from [IsometryWeights](IsometryWeights.md) supply the shared
sesquilinear matrix formulas; `sesqForm_congruence` retains the reversed
orientation. The extensionality theorem identifies equality under this pullback
with preservation of all vector values. This supplies the matrix congruence
condition used to define the actual isometry group.
