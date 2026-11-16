# Padding preserves the standard adelic compact subgroup

For every number field `F : Type u` and natural ranks `m ≤ n`, padding a
matrix by an identity block carries `PrimitiveAdelicHeight.standardCompact F m`
into `PrimitiveAdelicHeight.standardCompact F n`. The module is independent
of the proposed simple-root gauges. Worker 269 developed the matrix and
compact-membership proofs; Worker 254 extracted them and supplied the
restricted homomorphism and the point-level interface.

`map_padGL` proves that padding commutes with an entrywise ring homomorphism.
The proof checks the regions of the published `padGL_apply` entry formula.
`padGL_entries_mem` checks that every padded entry remains in a specified
subring: outside the leading block, the entries are zero or one.

`unitary_padGL` proves that padding preserves unitarity over a commutative
star ring. The conjugate transpose of a padded matrix is its padded inverse.
Multiplicativity of padding then proves the unitary identity. The proof
checks the two blocks and the two off-diagonal regions entry by entry.

For the finite adeles, `padGL_mem_standardIntegral` applies the subring-entry
result both to the matrix and its inverse. Thus it retains invertibility over
the integral finite adeles, rather than only integral entries. At the infinite
places, `padGL_mem_standardInfiniteCompact` commutes padding past each real
or complex coordinate map and applies `unitary_padGL`. This gives the real
orthogonal and complex unitary conditions. `padGL_mem_standardCompact`
combines the two projections using the published definition of the full
standard compact subgroup.

`padGLStandardCompactHom` bundles this restriction as a monoid homomorphism
between the two standard compact subgroups. Its coerced value is exactly the
published matrix padding map. `pad_mem_standardCompact` transports the same
membership assertion to actual adelic group-scheme points by
`GeneralLinearGroupPoints.adelicEquiv` and `Unfolding.adelicEquiv_pad`.
The results include `m = 0` and `m = n`; no additive-quotient compactness
hypothesis is needed.

This is internal algebraic infrastructure derived from the Library's matrix
padding and its orthogonal/unitary/integral standard compact construction.
It asserts no Whittaker majorization, integration formula or convergence.
