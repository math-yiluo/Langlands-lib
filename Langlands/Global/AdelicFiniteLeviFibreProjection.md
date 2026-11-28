# Finite assembly from cuspidal Levi fibre vectors

For a standard parabolic \(P=MU\), fix the positive central torus data of
`normOneDecomposition` for \(M\). Write \(p(b)\) for its positive point map and
\(\delta\) for the modulus of \(P\) on \(M(\mathbb A)\). The positive Haar
measure is normalized so that its product with norm-one Haar gives Levi Haar.
The construction uses right invariance of norm-one Haar and the full cuspidal
subspace of \(L^2\) on the positive rational quotient, with its measure
transported from \(M(F)\backslash M(\mathbb A)^1\).

Take a finite family of ambient compactly supported continuous kernels
\(\beta_l\), ambient points \(k_l\), a function \(\varphi\), and a real
coefficient \(c\). The role of the kernels and base points in the Iwasawa
formula is given by `leviPairing_rightConvolution_eq_iwasawa_finite`. Write
\(L_l(g,m)=\operatorname{radicalKernel}(\beta_l,g,1,m)\) and
\(\varphi_l(m)=\varphi(\iota(m)k_l)\), where \(\iota\) is the Levi inclusion.
Set \(d(t)=\delta(p(t))^{-1}\).

`finiteLeviFibreVector` is \(c\) times the sum over \(l\) of the
`cuspidalFibreVector` integrals formed with \(L_l(k_j,-)\), \(\varphi_l\), and
\(d\). For fixed \(j\) and \(b\), `inner_finiteLeviFibreVector` computes its
pairing against a cuspidal class \(v\) from the convergent vector integrals. With
the inner product linear in the second entry, the integrand at \(t\) and
\([y]\in M(F)\backslash M(\mathbb A)^1\) is

\[
  d(t)\,\varphi_l(y\,p(b)p(t))\,
     \overline{\operatorname{normOnePartialConvolution}
                      (L_l(k_j,-),v)(y\,p(t))}.
\]

The proof applies the inner product formula for each summand and then uses
linearity. This is the recentered form of the fibre integral at
\(\iota(p(b))k_j\) suggested by the finite Iwasawa formula and the
left-Levi covariance of the radical kernel.

`finiteLeviFibreVector_properties` assumes the norm-one partial convolution
rapid decay proposition and the adelic test function property for
\(L_l(k_j,-)\). It also assumes that \(\varphi\) is left invariant under the
parabolic quotient subgroup, continuous, and of height growth for a
positive-size closed matrix embedding. The embedding restricts to the Levi.
Submultiplicativity of height controls translation by each \(k_l\).
Rounding the input height exponent up to a natural number gives a common
degree for the fibre growth bounds. The Bochner integral construction gives
convergence, strong continuity in \(b\), and a polynomial bound on each
vector norm in the height of \(p(b)\).

`finiteLeviFibreProjection` smooths the \(j\)-th vector with the kernel
\(\beta_j\) by `leviFibreSmoothing`, sums over \(j\), and multiplies by \(c\).
For continuous vector families with the given polynomial bound,
`isModerateContinuousOnParabolic_finiteLeviFibreProjection` proves
continuity, left invariance on the parabolic quotient, and moderate growth.
The growth proof assumes an Iwasawa compact for \(P\) and a positive-size
closed matrix embedding of \(G\). It uses `hasHeightGrowth_leviFibreSmoothing`
term by term. These results provide the regularity step for the projection
characterization in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, §6.2, equation (6.8), using the parabolic integration
convention of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series*, I.1.13.
