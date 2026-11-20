# Levi and Weyl coefficients in the discrete comparison

The `Langlands.TraceFormula.CoordinateLevi n` index is a finite partition
of the `n` coordinate lines. It labels the block-diagonal Levi containing
the fixed diagonal torus in `GL_n`, with no ordering on the blocks. Its
`internalWeylOrder` is the product of the factorials of the block sizes,
and `IsRelativeWeyl` retains precisely the permutations preserving the
sizes. The ambient diagonal Weyl group has order `n!`.

For a block permutation `s`, `quotientWeylMatrix` is the permutation
matrix minus the identity plus the averaging projection onto constant
coordinates. The determinant is the determinant of `s - 1` on the quotient
by the constant coordinates. Indeed, the added projection acts by the
identity on the constant line and by zero on the complementary trace-zero
space. The absolute determinant is `regularDeterminant` and the regular
relative Weyl elements form `regularWeyl`. The coefficient
`discreteWeight` is the order of the internal Weyl group divided by `n!`
and then multiplied by the reciprocal of the absolute determinant. It is
used on both sides of III.(4.1)–(4.2), before the separate degree factor
multiplying the twisted distribution.

`CyclicRegularWeylDeterminantStatement` gives the regularity criterion and
the determinant of a full block cycle, including the single-block case.
Subtracting the invariant constant eigenline from a cycle leaves the
nontrivial roots of unity as eigenvalues. The product of the absolute
values of their differences from `1` is the length of the cycle.

`CyclicEqualBlockLeviCountStatement` states the counting in III.4.2(e).
For `l` positive-size blocks of the same size `m`, permutations of the
`m*l` coordinate lines act transitively on their unordered partitions.
The stabilizer has order `(m!)^l l!`, from permutations within blocks
and permutations of blocks. Once the intertwining comparison equates
all the `l!` reorderings on each of the coordinate Levis, multiplying
the count and reorderings by the internal/ambient Weyl ratio gives one.
The remaining coefficient is the reciprocal of the cycle determinant.

The matrix with an added averaging projection is a derived coordinate
model for Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula* (1989), II.(9.2) printed p. 132, III.(4.1)–(4.2)
printed p. 203, and the count and determinant in III.4.2(e), printed pp.
207–209. Registered source `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
