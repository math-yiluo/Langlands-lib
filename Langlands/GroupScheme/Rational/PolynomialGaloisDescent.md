# Finite-Galois descent of polynomial points

This internal construction extends the coefficientwise fixed-field argument
in `Absolute.LaurentGaloisDescent` to multivariate polynomial coordinates.
It is intended as infrastructure for constructing actual finite-Galois norm
morphisms from central additive subgroups. No split-unipotence descent theorem
is asserted here.

`PolynomialGalois.mem_range_extend_iff` applies the finite-Galois fixed-field
theorem to every coefficient. Its algebra-map construction descends an
invariant polynomial-valued algebra map and proves that extending it recovers
the original map uniquely. The variables are unchanged throughout, and the
argument does not divide by the extension degree. Both fields and the
polynomial variable type lie in the same universe; the source algebra can
lie in an independent universe.
