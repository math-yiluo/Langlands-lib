# Parameter-dependent right translation of Eisenstein sections

The Library writes the parameter twist as
\(\phi_\lambda(x)=\phi(x)\exp\langle\lambda,H_P(x)\rangle\).
`parameterTwistEquiv` is this scalar multiplication and its inverse
on the space of functions on \(G(\mathbb A_F)\). Transport positive
right translation along this equivalence to obtain the action on the
untwisted carrier. Its multiplier is the height power at \(xd\)
divided by the height power at \(x\), where \(d\) is the translating
element.

The height is right invariant under the Iwasawa compact subgroup, so
the transported action there agrees with ordinary translation at every
parameter. Invariance of the height under left rational parabolic points
shows that the action retains left rational parabolic invariance of the
section. Each summand of the Library's actual Eisenstein series for
the transported section equals the original summand at \(xd\), by
inverse cancellation and associativity. This gives covariance of the
unconditional sum, hence also covariance wherever the defining series
converges. Along a complex affine parameter line, the height powers
are exponentials of affine linear functions. Since they never vanish,
the ratio and each translated section value are holomorphic.

This implements the right-translation part of the covariance for the
varying induced actions in R. P. Langlands, *On the notion of an
automorphic representation* (1979), proof of Proposition 2, printed p. 206,
PDF p. 201 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`).
The carrier here is the algebraic space of scalar functions. To apply
this part to an analytic family of cuspidal sections, the action must
also be identified on the particular inducing subspace.
