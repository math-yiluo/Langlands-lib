# Global bounds from geometric approximation on a filtration

`GeometricApproximationBoundStatement` applies to a linear map \(T:V\to E\) of complex normed spaces and an increasing exhaustive filtration \(W_j\) of \(V\). Suppose \(\|T v\|\le C b^j\|v\|\) on \(W_j\), with \(b\ge1\). An approximation \(P_j v\in W_j\) preserves each fixed layer and satisfies \(\|P_j v-v\|\le a^j p(v)\), where \(a\ge0\), \(ab<1\), and \(p\) is nonnegative. Then \(\|T v\|\le C'(\|v\|+p(v))\) for a single \(C'\).

`geometricApproximationBound` estimates \(T(P_{j+1}v-P_jv)\) using the bound on \(W_{j+1}\) and the sum of the two consecutive approximation errors. Its geometric majorant is proportional to \((ab)^j p(v)\). A finite telescoping sum bounds \(T(P_jv)\) uniformly. For each fixed \(v\), the approximants remain in a layer containing \(v\), and the fixed bound on that layer shows that their images converge to \(T v\). Taking the limit in the uniform bound proves the assertion.

This estimate applies to polynomial filtrations sampled at dyadic scales, with \(p\) a finite sum of derivative norms.
