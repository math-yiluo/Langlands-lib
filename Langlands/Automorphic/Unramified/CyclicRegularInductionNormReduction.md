# Regular cyclic induction from existence and Euler recovery

`Langlands.Automorphic.Unramified.CyclicRegularInductionNormReductionStatement`
concludes the published `CyclicRegularInductionStatement` from actual regular
weak induction existence and cuspidal Euler constituent recovery. Both fields
and both presentation universes are independent. The conclusion keeps the
arbitrary cyclic degree, generator, norm-kernel character, unitary central
character and regularity assumptions. The existence premise supplies the
multiplied rank and an actual lower cusp with a genuine weak induction from
the upper cusp.

`cyclicRegularInductionNormReduction` proves the implication. At each retained
base place, embed the chosen base uniformizer into each completion above it.
The local norm of this unit is the uniformizer raised to the local degree,
which equals the residue degree because the weak induction relation supplies
ramification index one. The coordinate formula for the norm of an idèle
supported at that upper place gives the same power in the base idèle classes.
Triviality on norms gives `η_v(ϖ_v)^f = 1` at every such place. The coordinate
argument of `ideleClassNorm_ofAdicCompletion` applies to the underlying norm
maps with independent field universes.

The finite-order determinant twist gives a genuine presentation of the
actual twisted lower class. It scales the lower spectrum by `η_v(ϖ_v)`.
The induced polynomial has one factor in `X^f` for each upper place, so
the substitution `X ↦ η_v(ϖ_v) X` preserves all factors. Therefore the
twisted class is a second weak induction of the same upper cusp. The
published `weakInductionUniqueness_of_cuspidalEulerConstituentRecovery`
identifies every such class with the witness, including the twist, by
comparing the attached Euler polynomials of the singleton families.

The implementation is a derived reduction of Arthur and Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), Chapter III, Definition 6.1 and Theorem 6.2, printed pp. 215–217,
and Lemma 6.4, pp. 217–218. The comparison by cofinite Euler polynomials
is the role of Chapter III, equation (2.4), p. 200. Harris (1998),
Proposition 4.8, pp. 202–203, uses this regular induction in the prime
orbit branch. The residue-degree power suffices for the polynomial
comparison, while exact local character order concerns the stronger
arithmetic assertion in Arthur–Clozel III.3.1, p. 201.
