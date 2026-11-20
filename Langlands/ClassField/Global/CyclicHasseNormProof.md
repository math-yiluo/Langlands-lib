# Proof of the cyclic Hasse norm theorem for principal ideles

Let the idele norm of \(b\in J_E\) be the principal idele of \(a\in F^\times\).
The class of \(b\) has trivial idele-class norm. By the Galois product formula,
its sum in the additive idele-class representation lies in the kernel of the
cyclic norm operator. The cyclic cohomology description in degree one and the
Library's vanishing of the first idele-class cohomology give a class \(c\) with
\([b]=g(c)/c\), where \(g\) is a cyclic generator.

Choose an idele \(d\) representing \(c\). The idele \(b/(g(d)/d)\) has identity
class, so it is the principal idele of some \(x\in E^\times\). The idele norm
is invariant under automorphisms, since right multiplication by an
automorphism permutes the terms of the Galois product and the idele inclusion
is injective. The correction therefore preserves the norm. Compatibility of
the idele norm with principal ideles and injectivity of the principal embedding
give \(N_{E/F}(x)=a\).

The proof uses the cyclic coboundary underlying the cohomology sequence
argument in J. S. Milne, *Class Field Theory*, version 4.03 (2020), Chapter VIII,
Theorem 3.1, printed p. 234 (PDF p. 243). The source citation is recorded in
`CyclicHasseNormStatement.md`.
