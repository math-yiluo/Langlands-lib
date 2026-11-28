# Taylor coefficients of an affine intertwining identity

`WeakTaylorAffineIntertwinerStatement` concerns a family of complex-linear maps
\(T(z)\) between two complex vector spaces. For each fixed source vector, the
family is analytic at zero after applying any algebraic linear functional on
the target. `HasWeakTaylorCoefficients` specifies coefficient maps \(B_d\)
by testing against the same functionals and dividing the \(d\)-th derivative
at zero by \(d!\).

Suppose \(T(z)(D+zN)=(D'+zN')T(z)\) near zero on each fixed source vector.
The coefficient identity is
\[
B_dD+B_{d-1}N=D'B_d+N'B_{d-1},
\]
where the terms indexed by \(d-1\) vanish at \(d=0\). The proof applies an
arbitrary algebraic linear functional to the affine identity and uses the
scalar Leibniz rule. Multiplication by \(z\) shifts the normalized
coefficients by one because only the first derivative of \(z\) is nonzero
at zero. The algebraic dual separates vectors, which yields the asserted
vector identity.
