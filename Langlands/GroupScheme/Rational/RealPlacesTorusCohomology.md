# Localization of torus cohomology at the real places

## Approximation of quotient points

`RealQuotientPointApproximationStatement` considers a surjection \(q:P\to Q\)
of tori over a number field \(F\). Given a point \(y_w\in Q(F_w)\) at every
real place \(w\), it gives a single \(z\in Q(F)\) and points \(x_w\in P(F_w)\)
with \(y_w=z_wq_w(x_w)\). The statement uses actual scheme sections at
each field and the base-changed morphism \(q_w\).

`realQuotientPointApproximation` applies `realTorusPointApproximation` to
the target torus \(Q\). The resulting discrepancy at \(w\) is the norm
of a point over the algebraic closure of \(F_w\), a finite extension of
degree two. Base change preserves surjectivity of \(q\), and surjectivity
over the algebraically closed field gives a lift of that point. Naturality
of the norm sends the norm of the lift to the correcting norm. The affine
point equivalence identifies extension of coefficients with base change of
the section, so the product equality holds in \(Q(F_w)\).

## Localization of cocycles

`realPlacesTorusCohomologySurjectivity` proves the Library proposition
`RealPlacesTorusCohomologySurjectivityStatement`. Resolve the given torus
\(T\) as the represented kernel of an fppf quotient \(P\to Q\) with \(P\)
induced and \(Q\) a torus. The base change of \(P\) is the Weil restriction
of the multiplicative group from the scalar extension of a finite product
of fields. This finite algebra over \(F_w\) is semilocal, so its Picard
group vanishes. The corresponding Weil restriction cocycles are
coboundaries on the affine faithfully flat pullback of the original field
cover. In particular the pushforward of each given torus cocycle becomes a
coboundary. Effective-epimorphism descent of the quotient of its
trivializing cochain gives \(y_w\in Q(F_w)\) and a lift on that same cover.
The difference of the two pullbacks of the lift is the given
kernel-valued cocycle.

Approximation of these quotient points supplies \(z\in Q(F)\) with the
stated local discrepancies. The quotient morphism is smooth because its
represented kernel is smooth and the quotient is flat, surjective and
quasi-compact. The fibre over \(z\) is therefore smooth and nonempty after
extension to the original field cover \(L\). It has a point over a finite
separable extension \(E/L\). The differences of the two pullbacks of this
lift define a global cocycle on the cover by \(E\). Base change of the
global obstruction and refinement of each local obstruction identify both
cocycles with obstructions of quotient points on the same cover at \(w\).
Since their quotient points differ by \(q_w(x_w)\), the comparison lemma
gives a twist relating the two cocycles there.

The induced-torus resolution, Hilbert 90 and quotient approximation follow
the cohomology argument in Platonov and Rapinchuk, *Algebraic Groups and
Number Theory* (1994), Proposition 6.17, pp. 337–338, and §7.3,
Corollary 2, pp. 418–419. The Lean proof obtains the quotient approximation
from the proved real norm factorization and performs the boundary
comparison on finite separable covers.
