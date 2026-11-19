# Convergence of the local equal-rank integral from logarithmic torus bounds

Write \(P(x)=\sum_i \max(x_i,0)\) and \(Q(x)=P(-x)\).
The logarithmic kernel bound assumes a fixed exponent \(M\ge 0\)
such that for every \(L\ge 0\) the norm of the coefficient product before
the determinant twist is bounded by \(C_L e^{M Q(x)-L P(x)}\).
The estimate is uniform over the right unitary factor. It concerns the
product of both coefficient values and the test function of the last row.

If the coefficient product is continuous and the product of the two
coefficients is left \(N\)-invariant, multiplying by the determinant
power gives a continuous quotient integrand. This uses continuity through
the open quotient map and evaluation at any representative.
At the positive diagonal and the unitary factor, the squared determinant
norm is \(e^{2\sum_i x_i}\). The norm of the determinant power with
parameter \(s\) is therefore \(e^{2\operatorname{Re}(s)(P(x)-Q(x))}\).

For the threshold \(b\) from `ComplexLocalEqualBoxIntegrability.lean`,
take \(\operatorname{Re}(s)>(M+b)/2\) and use
\(L=2\operatorname{Re}(s)+b\). The resulting norm is bounded by
\(C_L e^{-b(P(x)+Q(x))}\). The box integration result proves integrability
on the stated half-plane for the exact quotient measure.

This internal implication implements the determinant exponent part of
the absolute convergence argument for Jacquet's integral (2.6) and
Lemma 3.5, printed and PDF pp. 6 and 14 of *Archimedean Rankin–Selberg
integrals* (2009).
