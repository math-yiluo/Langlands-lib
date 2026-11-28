# Exponential coordinates on congruence subgroup intersections

Let \(F\) be a proper, nontrivially normed characteristic-zero ultrametric field and
let \(A,B\) be finite-dimensional proper ultrametric normed \(F\)-algebras with the
Borel measurable spaces on the algebras and their unit groups. For a positive radius
\(r<1\), write \(L_A(r)\) for the closed additive ball around zero and \(K_A(r)\) for
the unit subgroup defined by \(\lVert k-1\rVert\le r\). Use the same notation for \(B\).

`ExponentialSubgroupIntersectionStatement` gives positive radius bounds inside the
convergence balls in both algebras. For radii within those bounds and an \(F\)-algebra
homomorphism \(i:A\to B\), assume \(i(L_A(r))\) lies in the union of the
algebra-automorphism images of the convergence ball in \(B\). The exponential then
gives a homeomorphism from
\(L_A(r)\cap i^{-1}(L_B(s))\) to the compact open subgroup
\(K_A(r)\cap (i^\times)^{-1}(K_B(s))\) of \(K_A(r)\).
The homeomorphism sends negatives to inverses and commutes with \(i\) in exponential
coordinates.

The proof uses commutation of the exponential with continuous algebra homomorphisms
on the convergence ball. If \(i^\times(\exp X)\) lies in \(K_B(s)\), its small
exponential coordinate in \(B\) equals \(i(X)\) by injectivity on the union of
automorphism images. This identifies the subgroup as the image of the stated lattice.
The chart restricts from the chart for \(K_A(r)\). The Haar comparison restricts as
well, and the measure on the intersection is the restriction in subgroup coordinates
of the \(k-1\) normalization from \(K_A(r)\).

This supplies the exponential chart and Haar comparison used in the compact
intersection calculation of Clozel, *Characters of nonconnected, reductive p-adic
groups*, §3.6, Lemma 9, p. 158. The saturation hypothesis permits an algebra
automorphism that need not preserve the norm.
