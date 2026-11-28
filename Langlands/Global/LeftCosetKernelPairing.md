# Transposition of a kernel pairing on a left Haar quotient

Let \(H\) be a locally compact Polish group with right-invariant Haar
measure and let \(\Gamma\) be a discrete subgroup. Write \(X=\Gamma\backslash
H\) with the Haar quotient measure. For an integrable kernel \(K\) on
\(H\), an integrable function \(v\) on \(X\), and a bounded measurable
function \(t\) on \(X\), `integral_integral_kernel_swap` gives

\[
\begin{aligned}
&\int_X \left(\int_H K(x^{-1}y)v([y])\,dy\right)\overline{t([x])}\,d[x]\\
&\qquad=\int_X v([y])\left(\int_H K(x^{-1}y)\overline{t([x])}\,dx\right)\,d[y].
\end{aligned}
\]

The integrand on \(H\times H\) is invariant under simultaneous left
translation by \(\Gamma\). With \(y=xz\), the corresponding integrand
with \([y]\) as the quotient variable and \(z\) as the group variable
is \(K(z)v([y])\overline{t([y z^{-1}])}\). Its absolute value is
dominated by a constant times the product of \(|K(z)|\) and
\(|v([y])|\). The skew change of variables
\(([x],z)\mapsto([xz],z)\) preserves product measure because each right
translation preserves quotient Haar. The domination transfers through
this map and Fubini gives the equality. The final change of variables
uses invariance of Haar under inversion for the unimodular group.

This is a measure-theoretic transposition for the norm-one Levi pairing
in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §6.2, equation (6.8). In that application \(v\) is a
representative of an \(L^2\) class on a quotient of finite volume.
