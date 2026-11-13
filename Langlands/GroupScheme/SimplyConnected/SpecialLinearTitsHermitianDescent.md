# A Hermitian form from an outer discrepancy

Author: Worker 239.

This internal unit works over arbitrary fields `K`, `L` and `M` in the
same universe. The extension `M/K` is finite Galois, `L/K` is Galois, and
`f : L →ₐ[K] M` is a specified embedding. A local special-linear
presentation `E` over `Spec M` is supplied. Its discrepancies are assumed
trivial on the subgroup fixing the image of `f`, on every relative test
scheme and every cover point.

The first descent result assumes an outer representative `X` for one
automorphism `σ` of `M/K`. Since `L/K` is Galois, the range-fixing subgroup
is normal. The previously proved outer-discrepancy algebra shows that its
elements preserve the conjugation action of `X` on `SL(M)`. Projective
matrix descent then supplies `Y ∈ GL(L)` whose image is a unit scalar
multiple of `X`. Scalar centrality preserves the original all-test outer
action, so the image of `Y` is still an outer representative.

Now supply a nontrivial field involution `c` of `L` and assume
`σ(f(z)) = f(c(z))` for every `z`. Involutivity implies that `σ²` belongs
to the range fixer. Composing the outer representative with itself gives
a scalar equation over `M`. The coefficient identity intertwining `σ`
and `c` identifies its left side with the image of `Y θ(c(Y))`, where
`θ` is inverse transpose. Reflection of scalar matrices along a field
embedding gives `Y θ(c(Y)) = a I` for a unit `a` of `L`.

The established Hermitian normalization applies to `Y⁻¹`: its adjoint
is `a Y⁻¹`, and a scalar multiple is a nonsingular Hermitian Gram matrix.
The elementary Hilbert 90 argument used by that normalization works in
every characteristic, including characteristic two. Its inverse Gram
matrix induces the same conjugation as `Y` after every coefficient
homomorphism. This retains the outer formula on every test scheme.

Two automorphisms with the same restriction to `f(L)` differ by an
element of its fixer. Consequently the same inverse Gram matrix
represents every automorphism restricting to `c`.
`outerHermitianForm` chooses the resulting actual `HermitianMatrix.Form`;
`outerHermitianForm_spec` records this all-test property.

These arguments compose the imported projective descent, outer
discrepancy and Hermitian normalization results. They construct neither
the initial cover nor its inner trivialisation, and do not assert the
final presentation of an outer type A group. A separable quadratic
extension supplies the Galois field and nontrivial involution required
here, but the unit takes those data as inputs.
