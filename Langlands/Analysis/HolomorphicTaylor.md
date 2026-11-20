# Formal Taylor series of holomorphic functions

`holomorphicAtSubring z` is the ring of complex-valued functions on
\(\mathbb C\) that are analytic at \(z\). `holomorphicTaylor z` sends
such a function to the formal series with coefficient
\(f^{(n)}(z)/n!\). Additivity follows from differentiating sums.
Leibniz's formula and the binomial coefficient identity give the
Cauchy product, so the Taylor map is a ring homomorphism. Its
constant coefficient is the value at \(z\).

When the analytic order is finite, the derivative indexed by that order
is nonzero, so the formal series is nonzero. This construction allows
the determinant argument to use formal powers of a single parameter.
It is an internal analytic ingredient for R. P. Langlands, *On the
notion of an automorphic representation* (1979), Lemma 9, printed p. 207,
PDF p. 202 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`).
