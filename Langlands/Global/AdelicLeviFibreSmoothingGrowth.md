# Moderate growth of smoothed Levi classes

Fix a standard parabolic \(P=MU\), a compactly supported continuous
ambient kernel \(\beta\), and the central split torus and Haar data of
`leviFibreSmoothing`. Suppose a family \(w\) of Levi \(L^2\) classes is
bounded in norm by \(B H_M(p(b))^r\) for a positive-size closed
Levi embedding, where \(B\geq 0\), \(r\in\mathbb N\), and \(p\) is the
positive point map.

`exists_leviFibreSmoothing_mul_levi_bound` gives a bound of the form
\(L H_M(p(a))^r H_M(x)^d\) at an ambient point
\(\iota(p(a)x)g\), where \(x\) is norm one and \(g\) ranges over a fixed
compact set. The covariance formula changes the integration parameter to
give the family \(b\mapsto w(ab)\) and norm-one evaluation at \(x\).
The smoothing integrand has a common compact positive support. The
reflected kernels on this support have a common compact support on the
Levi and a common sup norm bound by continuity of the radical kernel.
The uniform norm-one partial convolution estimate controls evaluation
at \(x\), and submultiplicativity controls \(H_M(p(ab))\). The reciprocal
modulus and the remaining positive height factor are bounded on the
compact positive support, which has finite Haar mass.

For `hasHeightGrowth_leviFibreSmoothing`, the Levi embedding is the
restriction of an ambient positive-size closed embedding, and an
Iwasawa compact \(K\) is supplied for \(P\). Write a point as
\(\iota_U(u)\iota(m)k\) using Iwasawa and the Levi retraction. Radical
invariance removes \(u\) from the argument of the function. Height
domination for the representation through the Levi retraction bounds
the height of \(m\) by a power of the parabolic point's height. The
compact right factor makes the latter polynomially bounded by the
original ambient height. The positive factor estimate
`exists_adelicHeight_positivePointMap_le` and submultiplicativity then
bound the heights of the positive and norm-one factors of \(m\).
Applying the first bound with \(g=k\) gives height growth on the ambient
group.

These estimates supply the growth step for the kernel construction for
the pairings of Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, §6.2, equation (6.8), with the Iwasawa coordinates and
modulus of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series*, I.1.13.
