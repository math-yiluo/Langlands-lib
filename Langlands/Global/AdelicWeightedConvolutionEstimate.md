# Localized weighted adelic convolution estimate

Let \(\Gamma\) be a subgroup of the rational points of an affine group over a
number field, embedded by a closed matrix representation. The measure on
\(\Gamma\backslash G(\mathbb A)\) is the discrete quotient of the chosen adelic
Haar measure. Fix a compact set \(C\) in the adelic group and a compact set in
its finite factor. For each \(x\) whose finite component lies in that compact
set, suppose the image of \(xC\) is in a supplied domain \(S\) on which the
quotient measure has density at least \(b>0\) along that image. The pushforward of
ambient measure restricted to \(C\) under \(a\mapsto \Gamma xa\) is bounded by
\(B\operatorname{ht}(x)^d/b\) times the weighted measure on \(S\). The constant
\(B\) can depend on the two compact sets. The exponent is independent of both.

The proof first counts rational points in \(xCC^{-1}x^{-1}\), which bounds the
multiplicity on the left quotient of the translate \(xC\). It uses the discrete
quotient measure estimate, left invariance of Haar measure, and monotonicity of
restriction and density to obtain the weighted bound. The same measure bound
shows that a weighted \(L^2\) function pulls back to \(L^2\) on the compact
support with norm at most \(\sqrt{B\operatorname{ht}(x)^d/b}\) times the input
norm. A general Cauchy–Schwarz lemma applies this pullback bound to show
absolute integrability of the convolution integrand and bound its integral by
the product of the two \(L^2\) norms. This also covers bounded measurable
kernels supported in \(C\), since Haar measure is finite there.

This is the localized estimate underlying the integral-kernel argument of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §7.4(2), p. 216, drawing on Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.2.4–5, pp. 25–27.
The domain containment and density lower bound are supplied for the particular
translate. Differentiation and the geometry of the Siegel domains are further
inputs to the smooth estimate.
