# A finite subset model for the Koszul differential

This internal supporting module constructs the Koszul differential in subset coordinates.
For a linearly ordered finite set of indices and scalars `a i`, the coefficient
for adjoining `i` to a subset `s` is zero when `i` already belongs to `s`, and
otherwise is `(-1)` to the number of elements of `s` less than `i`, times `a i`.
The ambient module has a coordinate for every subset. The differential at `s`
sums the coefficients times the coordinates of `insert i s`.

Adjoining two distinct indices in the two possible orders gives opposite
coefficients, since exactly one insertion changes the parity of the second
sign. Repeated indices give zero. A finite-sum involution swapping the two
indices proves that the square of the differential is zero over any
commutative ring, including characteristic two.

`FiniteKoszulModule R ι n` is the function module on subsets of cardinality
`n`. `koszulExtend` extends a vector by zero to the ambient module and
`koszulRestrict` restricts an ambient vector to one degree. Their composite
is the identity, so extension is injective. `finiteKoszulDifferential` extends
a vector in degree `n+1`, applies the ambient differential, and restricts to
degree `n`. Its ambient image is supported in degree `n`: adjoining a new
index increases cardinality by one, while adjoining an existing index has
coefficient zero. Thus extension intertwines the differentials, and injectivity
of extension transfers the square-zero identity to the graded modules.

The residue-field application is separate from this internal construction.
No exactness or regularity of the generator tuple is asserted.
