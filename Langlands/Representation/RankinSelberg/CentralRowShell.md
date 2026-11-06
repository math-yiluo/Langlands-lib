# A positive row shell for central translation

This internal geometric construction uses the actual integer row lattice
for an arbitrary supplied p-adic topology `T`. Let `z` be the published
`centralSpectralElement T (n+1)`, the inverse-uniformizer scalar matrix.
Multiplication of a row by `z` multiplies each coordinate by the inverse
uniformizer.

`HasPositiveCentralRowShell T n` asserts the existence of a Schwartz–Bruhat
function `Φ` with `Φ(0)=1` such that `Ψ = Φ - rowTranslate z Φ` vanishes
at zero, equals one on the last row of the identity matrix, and takes
only the values zero and one.

`hasPositiveCentralRowShell` chooses `Φ` to be the indicator of the product
of `n+1` copies of the actual integer lattice `T.additiveLattice 0`.
The imported lattice topology results make this product compact and open.
If `xz` lies in that product, then every coordinate of `x` has normalized
absolute value at most one, since the normalized absolute value of the
inverse uniformizer is the residue cardinality, which is greater than one.
Thus the translated indicator is supported inside the original lattice,
so their difference takes only zero and one. Both indicators are one
at zero. The identity's last row belongs to the integer lattice, whereas
its translate by `z` has last coordinate of absolute value greater
than one. Their difference at that row is therefore one.

The construction is derived from the imported lattice geometry and
normalization identities. It asserts no convergence, integration,
rational continuation or pole.
