# Normalized brackets of opposite root vectors in SL₂

`lieMatrixLieHom` differentiates the inclusion of `SL₂` into `GL₂` and
applies the inverse of the dual-number matrix comparison
`GeneralLinear.DualNumber.pointKernelLieEquiv`. Its underlying map is
the usual matrix coordinate `SpecialLinear.FinSucc.lieMatrix`. The
comparison carries the tangent Lie bracket to the matrix commutator.

For each root of the diagonal torus, `exists_coord_of_mem_roots` gives
distinct indices \(p,q\) with root character \(w(p)-w(q)\).
`exists_normalizedRootVectors` lifts the traceless matrix units \(E_{pq}\)
and \(E_{qp}\) to Lie vectors \(e,f\) of opposite weights. The support
criterion for the diagonal torus gives the two weight equations, and the
\((p,q)\) entry gives \(e\ne 0\). The commutator of the two matrix units is
\(E_{pp}-E_{qq}\), whose commutator with \(E_{pq}\) is \(2E_{pq}\).
Injectivity of the matrix differential gives \([[e,f],e]=2e\) over
the base field.
