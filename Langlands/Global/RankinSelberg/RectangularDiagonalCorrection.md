# Diagonal corrections independent of the leading torus

This internal module separates the leading diagonal variable from the
Iwasawa factorization of the rectangular lower unipotent.
`paddedDiagonal d b` appends `d` units equal to one to a unit tuple `b`.
Its diagonal matrix is the two-block diagonal matrix with leading
diagonal `b` and trailing identity.

The rectangular matrix with leading diagonal `b` is exactly this padded
diagonal times `lowerBlockPair 1 x 1`. Consequently, if
`lowerBlockPair 1 x 1 = U*diag(c)*K`, the same `c` and `K` work for
every leading diagonal: the new diagonal is the coordinatewise product
of `paddedDiagonal d b` and `c`, and the new upper unipotent is the
diagonal conjugate of `U`. The implemented proof uses the published
two-block multiplication formula and
`IsUnitriangular.diagonal_conj`, followed by group cancellation.
It retains the factorization as an explicit premise.

Negating `x` gives the inverse lower unipotent. If all rectangular
entries have norm at most `C ≥ 1`, every entry of this lower unipotent
and its inverse has norm at most `C`; this follows by inspecting their
four blocks.

For any factorization `M=B*K`, bounds by `C ≥ 0` on the entries of
`M` and `M⁻¹`, together with bounds by one on `K` and `K⁻¹`, bound
all entries of `B` and `B⁻¹` by `n*C`. The proof writes
`B=M*K⁻¹` and `B⁻¹=K*M⁻¹` and uses the published entry estimate
for a matrix product. For an ultrametric norm, the sum is bounded by
the largest summand, giving `C` in place of `n*C`. In particular this
retains constant one on integral matrices. The statements apply to
all entries; for a triangular factor they control its diagonal
correction and its inverse.

The results are algebraic and local norm bounds. They do not prove a
global majorant, integrability, or the target Mellin statement.
