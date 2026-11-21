# Change of variables for twisted orbital integrals

`twistedOrbitalEquiv` proves `TwistedOrbitalEquivStatement` for topological
groups \(G\) and \(G'\) with Borel measurable structures and a continuous
group isomorphism \(e:G\to G'\) intertwining endomorphisms \(\theta\) and
\(\theta'\). For \(\delta\in G\), the theorem starts with an ambient measure,
a right-invariant measure on the twisted centralizer of \(\delta\), and a
compatible measure on its left coset space with the quotient Borel structure.
It pushes these measures forward along \(e\) and the induced isomorphisms on
the centralizer and its quotient. The resulting measure on the quotient for
\(e(\delta)\) is compatible. The orbital integrand of any complex-valued
function \(f\) on \(G'\) is integrable there exactly when that of \(f\circ e\)
is integrable for the original quotient measure. The two total Bochner
integrals agree under the same change of variables.

The intertwining identity sends \(x^{-1}\delta\theta(x)\) to
\(e(x)^{-1}e(\delta)\theta'(e(x))\). The proof restricts \(e\) to the
stabilizers of \(\delta\) and \(e(\delta)\) and sends a left coset represented
by \(x\) to the one represented by \(e(x)\). The Library's quotient measure
transport theorem gives compatibility for these three maps. The same identity
on coset representatives identifies the two integrands after pullback.

This is an internal change of variables for the twisted orbital integrals of
Getz–Hahn, *An introduction to automorphic representations*, §18.5. It gives
the quotient measure comparison needed when changing local matrix coordinates.
