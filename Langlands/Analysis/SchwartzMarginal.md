# Marginals of Schwartz functions on real vector spaces

`marginalCLM` is the continuous complex-linear map from Schwartz
functions on \(E\times F\) to Schwartz functions on \(E\), for
finite-dimensional real normed spaces \(E,F\) and an additive Haar
measure \(\mu\) on \(F\). `marginalCLM_apply` gives its value at \(x\) as
\(\int_F \Phi(x,y)\,d\mu(y)\).

In Euclidean coordinates, the second-variable integral is continuous
by dominated convergence using Schwartz decay in the integrated
variable. It is integrable by Fubini. Its Fourier transform equals the
restriction of the full Fourier transform to the first factor's frequency
subspace. The product inner product and the measure-preserving Euclidean
product equivalence implement this identity. The restriction map
preserves Schwartz functions because the inclusion is a linear
isometry. Fourier inversion then identifies the pointwise integral with
the inverse transform of this Schwartz restriction.

The construction for normed spaces transports to Euclidean spaces
through continuous linear equivalences and scales by the Haar measure
comparison in the second factor. The construction is a composition of
continuous linear maps.

This supplies the Schwartz marginal used for the off-diagonal
integration in Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§7.1, p. 44.
