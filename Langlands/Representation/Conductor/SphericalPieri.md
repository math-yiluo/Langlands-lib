# Integral-weight minuscule recursion in the symmetric Laurent algebra

This internal unit defines the elementary symmetric polynomials and the
normalized minuscule Hecke eigenvalues in the actual symmetric Laurent algebra.
For rank `n + 1`, the eigenvalue with index `k` is the elementary symmetric
polynomial `e_k` multiplied by
`sqrt(q)^(k * (n + 1 - k))`, with the positive real square root.
Evaluation at every tuple of complex units gives the existing standard
minuscule scalar. These definitions accept every natural `q`; the recursion
theorems below require `q > 0`.

`sphericalTorusLaurentPolynomial` is the normalized integral-weight Schur
expression on dominant weights and zero elsewhere. The unit proves its
minuscule recursion for every dominant integer weight when `q > 0`. First, evaluation at
unit tuples and the existing nonnegative Pieri recursion give the result on
nonnegative dominant weights. Subtracting the last coordinate gives such a
weight from any dominant integer weight. The constant-shift identity proved
in `SphericalCentral` then restores the original weight, including negative
coordinates. Every raised term has the same constant shift, so the determinant
unit factors out of the entire sum.

For the group calculation, `F` is a field with valuation `v` and a supplied
`IsUniformizingElement v ϖ`: `v(ϖ) < 1` and every nonzero field valuation is an
integer power of `v(ϖ)`. The character `θ` of the upper-unipotent group is
assumed trivial on its integral points (`IsIntegrallyTrivial v θ`).
Under these hypotheses, `sphericalWhittakerMinusculeSum` is the actual finite sum of the spherical
Laurent polynomial over the labelled minuscule representatives. The unit
identifies this sum at each dominant torus element with multiplication by the
specified Laurent eigenvalue. It uses the existing unipotent calculation:
integral radical entries do not change a dominant torus value, and counting
labels gives `q` to the number of radical pairs.

No characteristic-zero hypothesis is used. Subject to the supplied uniformizing
element and integral character triviality above, the field and valuation are
arbitrary. The label type is any finite type of cardinality `q > 0`, and its
chosen field-valued lifts must be integral. This torus calculation does not yet require
the lifts to represent all distinct residue classes. Extending the identity to
all group elements requires those residue-class conditions, right integral
invariance of the sum, and the standard character nontriviality condition.
Those extensions, its action on integrated model numerators, full ideal
stability, universal finite support and the essential-conductor target remain
separate obligations. The provenance is the implemented internal deduction
from the existing Pieri, central-shift and actual coset-value theorems.
