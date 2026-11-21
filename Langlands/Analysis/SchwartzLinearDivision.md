# Division of Schwartz functions by a linear form

For a real normed space \(E\) and a continuous real linear form \(\ell\),
`schwartzVanishingOnKernel ℓ` is the complex submodule of \(\mathcal S(E,\mathbb C)\)
consisting of functions that vanish on \(\ker\ell\). For \(\ell\ne0\),
`schwartzLinearDivision ℓ hℓ` is a continuous complex-linear map from this
submodule, with its induced topology, to \(\mathcal S(E,\mathbb C)\).
`smul_schwartzLinearDivision_apply` proves the identity
\(\ell(x)\,(\operatorname{div}_{\ell} f)(x)=f(x)\) at every \(x\).

This realizes Lemma 7 in E. Lapid, *On Arthur's asymptotic inner product formula
of truncated Eisenstein series*, Clay Math. Proc. 13 (2011), §7,
printed p. 325 (volume PDF p. 334). The registered source is
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`. Lapid uses Euclidean
spaces. The argument here works for the indicated real normed spaces and uses
the transverse derivative in the integral formula.

Choose \(v\) with \(\ell(v)=1\) and set
\(A_t x = x-(1-t)\ell(x)v\). The operator takes \(f\) to the average of
\(\partial_v f(A_t x)\) over \(0\le t\le1\). The integrand is jointly smooth in
\((x,t)\). `contDiffOn_infty_compactFamily_of_joint` gives smoothness as a map
to continuous functions on \([0,1]\) with the supremum norm. Integration on
that interval is bounded and linear. The fundamental theorem of calculus along
\(t\mapsto A_t x\) gives the multiplication identity since \(A_0 x\in\ker\ell\)
and \(A_1 x=x\).

For \(|\ell(x)|\le1\), the maps \(A_t\) have uniformly bounded operator norm and
\(\|x\|\le\|A_t x\|+\|v\|\). Evaluating the iterated derivative at each parameter
\(t\) and using the chain rule bounds the weighted \(n\)-th derivative of the
average by finitely many seminorms of \(f\) through order \(n+1\).
For \(|\ell(x)|\ge1\), the identity identifies the average with
\(\ell(x)^{-1} f(x)\) on the open complement of the kernel. There, at each point
with \(|\ell(x)|\ge1\), the norm of the \(i\)-th derivative of the scalar
reciprocal is at most \(i!\,\|\ell\|^i\). The product rule bounds the weighted
derivative on this region using the same finite set of input seminorms.
These estimates give the Schwartz decay and continuity. Complex linearity
follows from the complex linearity of the directional derivative and of the
integral.
