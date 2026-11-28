# Compact averages of algebraically compact-finite vectors

`CompactFiniteAverageStatement` concerns a complex representation of a compact topological monoid equipped with a finite Borel measure. Suppose each vector has finite-dimensional orbit span and each algebraic linear functional gives a continuous scalar orbit function. A continuous scalar weight \(a\) then defines a linear endomorphism \(A\) on the algebraic carrier by the identity
\[
\ell(Av)=\int a(k)\ell(\rho(k)v)\,d\mu(k)
\]
for every algebraic linear functional \(\ell\).

The proof sends the orbit span of \(v\) to the functions on its ambient algebraic dual by evaluation. The weighted orbit takes values in this finite-dimensional function space and its evaluations are integrable by compactness. `InductionStages.integral_mem` puts the pointwise integral in the same space, so it comes from a vector. Separation by the algebraic dual proves uniqueness, additivity and complex homogeneity.

This is the finite-dimensional integration argument underlying compact group averaging on Harish-Chandra modules. Its hypotheses are the compact finiteness and scalar continuity clauses of `IsRealGKModule` when the monoid is the orthogonal group.
