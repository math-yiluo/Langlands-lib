# Compact polynomial averages on real standard modules

For a polynomial \(\varphi\) in the matrix entries of \(O(n)\) and a real
invertible matrix \(g\), `averageMap` sends \(f\) to the function
\(x \mapsto \int_{O(n)} \varphi(k) f(xkg)\,dk\). It is an endomorphism
of the compact-finite real standard module and has finite-dimensional range.
The Haar measure may have any normalization.

On the compact group a change of variables expresses the operator with
kernel \(\varphi(x^{-1}y)\) acting on \(y \mapsto f(yg)\).
The separated-variable formula of `OrthogonalFinitePolynomial` places
the kernel columns in one finite-dimensional space. Pointwise integration
keeps the image in that space. The compact restriction is polynomial
and extends to the principal series by its diagonal sign covariance.
Iwasawa decomposition and the covariance of the original average identify
the extension on the whole group. Fubini interchanges the compact average
with each rotation Fourier integral, so the required coefficients vanish.

Restriction to \(O(n)\) is injective on the principal series. The finite
bound for the compact restrictions therefore gives a finite-dimensional
range on the actual standard module. This internal result uses the existing
principal series extension and finite-dimensional pointwise integration
theorems. It supplies finite-rank operators for comparing traces along
real standard intertwiners.
