# The elliptic centralizer quotient and orbit function for `GL_n`

`Langlands.TraceFormula.generalLinearEllipticCentralizer` proves
`GeneralLinearEllipticCentralizerStatement` with its universe parameter free.
The theorem gives finite volume for the rational left quotient of the norm-one
centralizer and integrability of each continuous compactly supported test
function pulled back to the centralizer quotient.

`GeneralLinearGroupPoints.normOneAdelicHomeomorph` identifies the norm-one adelic
points of the group scheme with the determinant-norm-one subgroup of `AdelicGL`.
Compatibility with `rationalEquiv` and `adelicHomeomorph_rational` identifies the
principal subgroups. At the specified finite place, the characteristic polynomial
is the scalar extension of the polynomial of the rational matrix. Separability
and irreducibility therefore descend to the number field. Irreducibility gives
positive degree and hence positive matrix rank.

`AdelicRegularCentralizerCompact` uses the characteristic field and the compact
norm-one idele fundamental set to prove compactness of the rational centralizer
quotient in the matrix model. The matrix homeomorphism gives a homeomorphism of
centralizers and respects the principal subgroups, so the induced homeomorphism
of the left quotients carries compactness to the group-scheme model.
`AdelicRegularConjugacy` proves closedness of the matrix orbit, by describing the
full adelic orbit as a characteristic-polynomial fiber and correcting conjugators
to have determinant norm one. Closedness pulls back along the matrix homeomorphism.

The proof then applies `twistedCentralizerAnalyticConditions_of_compact_closed`
with the identity automorphism. The norm-one group is locally compact and second
countable, hence σ-compact. Compactness gives finite mass for the compatible regular
measure on the rational centralizer quotient. For the orbital quotient, the
open mapping argument of `TwistedOrbitHomeomorph` identifies the left quotient
with the closed orbit. A continuous compactly supported test function restricts
and pulls back to a continuous compactly supported function there, which is
integrable for the compatible regular measure. The specialization uses the two
supplied Borel structures, the measures and their compatibility hypotheses.

In Getz–Hahn, *An Introduction to Automorphic Representations* (2024), the
norm-one measure convention comes from §2.6, especially equations (2.19)–(2.22)
on printed pp. 68–69. Theorem 18.2.5 on p. 479 assumes closed orbits and uses the
centralizer volume (18.14). Section 18.4 on p. 485 defines ellipticity by finiteness
of that volume for ordinary conjugation and uses the orbital integral (18.26) in
Corollary 18.4.1. This proof establishes the corresponding two analytic properties
from regular ellipticity at one finite place, using the Library's actual norm-one
points and compatible quotient measures. The retained source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
