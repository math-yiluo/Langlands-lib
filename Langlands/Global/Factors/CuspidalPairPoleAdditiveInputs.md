# Standard additive inputs for the ordinary pair integrals

The global additive character here is the Library's
`standardGlobalAdditiveCharacter`, which is trivial on the diagonal
number field. At each real place its restriction to a single
archimedean coordinate has additive scale one. At each complex place
its restriction is the scale-one complex trace character. To see this,
evaluate the global character on the inserted coordinate with zero
finite part. The mixed-space trace is the real coordinate at a real
place and twice the real part of the complex coordinate at a complex
place. The definitions of the local standard characters use those
same trace values in the exponential.

`standardGlobalAdditiveSupport` chooses a finite set containing the
conductor support of this character. Any finite enlargement also has
the support property, so the exceptional sets of both spectral
presentations may be included. The canonical finite components and
their self-dual measures come from the published additive input theory.

The local scales agree with H. Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), the standard character convention on p. 10 and
Appendix 16.1, pp. 109–110, in the author-posted version. The use of a
global character and an exceptional finite set is in J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §4, printed p. 218
(PDF p. 221). The Lean proof uses the Library's established global
character and coordinate trace formulas.
