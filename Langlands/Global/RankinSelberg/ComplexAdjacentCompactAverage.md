# Compact averaging in the unfolded adjacent-rank integral

Let \(D\) be the smaller quotient measure, \(\nu\) a Haar measure on
\(\operatorname{GL}_{r+1}(\mathbb C)\), and \(\kappa\) a finite measure on
\(U(r+1)\). Let \(u\) be a continuous map from \(U(r+1)\) to itself and \(w\)
a continuous complex weight. The square Schwartz test \(\Phi\) has a
finite-dimensional span of left unitary translates. Assume that averaging
\(\Phi(u(k)^{-1}X)\) against \(w(k)d(\det u(k))^{-1}\) reproduces \(\Phi\).
For opposite-character Whittaker vectors \(W,V\), `complexAdjacentCompactAverage`
shows that the unfolded kernel remains integrable in a right half-plane when
\(V(gz)\) is replaced by
\[
  \int_{U(r+1)} w(k)V(g\,u(k)\,z)\,d\kappa(k).
\]
Its integral over the group and quotient is unchanged by this substitution.

The proof chooses a basis of the translates of \(\Phi\), each represented by
a Schwartz function. Evaluation at matrices spans the dual of this
finite-dimensional space, so the coordinates of the compact family of
translates are continuous. Applying `complexAdjacentConvergence` to the
basis tests gives a common half-plane of absolute convergence for the joint
kernel with the compact variable. The map \((k,z,q)\mapsto(k,u(k)z,q)\)
preserves the product measure by left Haar invariance. Unitarity makes the
absolute determinant of \(u(k)\) equal to one, and the reproducing weight's
determinant twist cancels the remaining compact character factor. Fubini
then gives the asserted equality.

This is an auxiliary form of the compact averaging in Section 8.3 of Hervé
Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009, DOI
`10.1090/conm/489/09547`. The compact map \(u\) accommodates both the ordinary
identity action and the inverse-transpose action for the Fourier transform.
