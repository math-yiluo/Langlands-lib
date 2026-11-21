# Openness of twisted diagonal saturation

Let \(E\) be a normed field of finite dimension over a complete nontrivially
normed field \(F\), let \(\tau\) be an \(F\)-algebra automorphism of \(E\), and
let \(K\) be an open subgroup of \(\mathrm{GL}_n(E)\). Suppose that the
diagonal entries of a family of diagonal invertible matrices range over
an open subset of \(E^n\). At each tuple \(a\) in the family assume that
\(a_i\tau(z)=a_jz\) implies \(z=0\) for distinct \(i,j\).
`isOpen_twistedDiagonalSaturation` shows that the \(K\)-twisted saturation
of the family is open.

At a diagonal with entries \(a_i\), use a single matrix variable \(X\).
Its off-diagonal entries are the perturbations of the identity conjugator
and its diagonal entries perturb the original diagonal. The strict
derivative of the resulting twisted conjugation map at \(X=0\) sends a
diagonal coordinate to itself and an off-diagonal coordinate \(z\) to
\(a_i\tau(z)-a_jz\). The kernel condition and finite dimension give
surjectivity. The strict inverse function theorem gives a neighborhood of
the original diagonal in the image. The open constraints on the
conjugator and diagonal can be kept by restricting the source to a
neighborhood of zero. Twisted conjugation by \(K\) transports the
neighborhood to each point of the saturation.

This is the submersion argument for strictly decreasing weights in
Henniart–Lemaire, *Changement de base et induction automorphe pour
GL(n) en caractéristique non nulle* (2011), I.4.1, pp. 26–27.
