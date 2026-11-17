# Whittaker bounds through actual adelic Iwasawa factors

This internal helper factors an actual adelic general linear group point as a
full unipotent point times an idelic diagonal times a standard compact point.
It applies the published triangular-times-compact factorization and removes
the diagonal of the triangular factor using `TriangularDiagonal`. The
published matrix characterization of the actual unipotent subgroup verifies
that the first factor is an element of that subgroup.

Whittaker equivariance and the unit norm of the standard generic character
make the Whittaker norm left unipotent invariant. The determinant norm is
also left unipotent invariant. Thus a real-valued diagonal estimate uniform
over the standard compact subgroup transfers to every adelic point whenever
its proposed majorant has the two invariances and the indicated diagonal
profile. The final conversion to extended nonnegative reals uses positivity
of the determinant power.

These results are derived from the imported algebraic factorization,
Whittaker equivariance, and determinant identities. They do not assert
integrability or construct the majorant.
