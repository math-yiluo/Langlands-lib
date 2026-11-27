# Restriction of the unitary discriminant to its quadratic center

For an algebra over a quadratic center \(L/F\) with a unitary involution
inducing the nontrivial center automorphism, fix a matrix splitting chart
of size \(2m>0\) over an extension \(M\) of \(L\).
`relativeRestriction_relativeDiscriminantClass` computes the restriction
along \(\operatorname{Gal}(M/L)\to\operatorname{Gal}(M/F)\).
Every element in the image fixes the center, so
the twisted matrix lifts act by ordinary semilinear conjugation in the
original splitting chart. Their scalar factor set represents the relative
Brauer class of that chart. The discriminant factor set on this subgroup is
its \(m\)-th power, which represents \(m\) times the relative Brauer class.

For a central simple algebra \(A/L\) and a finite Galois splitting stage
\(M/F\) containing \(L\), `scalarExtension_discriminantClass` gives the
corresponding identity in the algebraic Brauer group of \(L\). It uses
the induced finite Galois extension \(M/L\). The proof extends the
matrix chart for the discriminant representative along \(F \to L\)
inside \(M\) and applies the relative comparison to the resulting chart.
The fields, the original algebra, and the discriminant representative
share a universe.

This is the Brauer class identity of Knus, Merkurjev, Rost and Tignol,
*The Book of Involutions* (1998), §10.E, Proposition (10.30), printed p. 129,
together with the class of the \(\lambda\)-power in §10.A, (10.4)(a),
printed p. 116.
