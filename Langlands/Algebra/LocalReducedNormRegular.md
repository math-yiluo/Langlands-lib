# Regular representatives in local reduced-norm fibers

`Langlands.CentralSimple.LocalReducedNormRegularStatement` says that
an element of nonzero reduced norm in a finite-dimensional central
simple algebra has a representative of the same reduced norm with
separable reduced characteristic polynomial. The ground field is
complete, nontrivially normed and of characteristic zero.

The reduced norm is continuous in finite basis coordinates because
it is a polynomial. Near the original element, the ratio of its new
norm to the original norm lies in the image of the unit power map
for the reduced degree. The Library's neighborhood theorem for
powers gives this neighborhood. It contains a box of infinite
coordinate sets, so the regular basis-box theorem gives a regular
element there. If the norm ratio is \(s^d\), with \(s\) a unit and
\(d\) the reduced degree, multiplying the new element by
\(s^{-1}\) restores the original norm and preserves separability
of the reduced characteristic polynomial.

This internal lemma derives the regularity step for the local
reduced-norm problem from polynomial avoidance and the local
power-map neighborhood theorem.
