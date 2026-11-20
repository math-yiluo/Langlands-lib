# The Whittaker differential operator in matrix coordinates

This internal construction expresses the Hessian sum from
`ComplexLocalWhittakerMatrixDifferential` as a `CoordinateScalarOperator` of
order two. It uses the real matrix-unit basis and reindexes it by `Fin d`,
where \(d=2n^2\).

For a matrix \(h\), write \(h e_i=\sum_p c_{ip}(h)e_p\). The coefficient of
the ordered second derivative in directions \(e_p,e_q\) is
\(\sum_i c_{ip}(h)c_{iq}(h)\). The lower-order coefficients vanish. The
coordinate functions \(c_{ip}\) are real linear, so all coefficients of the
operator are real analytic.

Expanding each Hessian evaluation on \(h e_i,h e_i\) in the basis and
reordering the finite sums proves the action formula. The same expansion on a
real covector \(\xi\) gives the principal symbol
\(\sum_i \xi(h e_i)^2\). For invertible \(h\), the vectors \(h e_i\) span the
matrix space, so the sum is positive for \(\xi\ne 0\).
