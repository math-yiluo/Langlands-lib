# Local bounds from rectangular trailing minors

This internal helper applies the exact determinant identities from
`RectangularIwasawaMinors` to local bounds. It defines
`trailingDiagonalProduct a d B` as the product of the last `d` diagonal
entries of an `(a+d)` by `(a+d)` matrix.

For a field with any valuation into a linearly ordered commutative group
with zero, suppose `B` is upper triangular and every entry of `K` is in
the valuation ring. Every bottom `d` row minor of `B*K` has valuation
at most the valuation of `trailingDiagonalProduct a d B`. The proof
factors the determinant exactly and uses the published
`Cartan.det_mem_integer` for the minor of `K`.

If `lowerBlockPair g x 1 = B*K` as matrices, the replaced-column minor
identity bounds every `x i j` by this product. The principal trailing
minor shows that the product's valuation is at least one. If it is also
at most one, all entries of `x` are in the valuation ring. These bounds
have constant one, which is necessary for support control at almost all
finite places.

Over any normed field, the same argument gives a bound with constant
`d!` when the entries of `K` have norm at most one. The implemented
proof first bounds a determinant by its Leibniz sum: each signed product
has norm at most one, and there are `d!` permutations. It then applies
the same exact trailing-minor factorization and the two minor identities
for `lowerBlockPair`.

For an `RCLike` field, a final corollary specializes the coordinate norm
bound to a unitary right factor, using the published
`TriangularUnitary.norm_le_one_of_mem_unitaryGroup`.

All factorization and entry hypotheses are explicit; these lemmas do
not construct an Iwasawa factorization, and the valuation result does
not identify a finite completion's norm. The three-block chart, simple-root
comparison, global support control and Mellin convergence remain
separate obligations. No analytic convergence assertion is made here.
