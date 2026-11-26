# The conductor formula from completed standard equations

`cuspidalSigmaLiftConductorFromCompletedEquations` proves an implication to
the four-universe `CuspidalSigmaLiftConductorStatement`. Its premises are
`CuspidalPairGlobalFunctionalEquationStatement` over small number fields
and `CuspidalSigmaLiftGlobalFactorDataStatement` for the local input of
rank at least two.

The global factor data supply a cyclic extension of number fields and a
pair of compatible completion isomorphisms with a single place above the
distinguished place. They also supply actual cuspidal presentations
identifying the two distinguished representations up to unramified
determinant twists. The lower distinguished component is supercuspidal.
`HasGlobalStandardFactorComparisons` requires separation of the roots of
the upper forward and reflected dual Euler polynomials there. Away from
that place the premise compares the grouped forward and dual finite Euler
values and the grouped positive epsilon bases for the global norm-character
twists and the upper presentation.

In rank one, the proof uses the conductor identity
`cuspidalSigmaLiftConductorRankOne`. In greater rank, it chooses actual
contragredient presentations and uses `distinguishedNormCharacters` for
the global twist family. Supercuspidality of the lower components makes
both their standard Euler polynomials one at the distinguished place.
The completed-equation comparison then gives a comparison of epsilon
monomials at the two completions. The standard additive characters are
related by the trace. Pulling the comparison back to the original fields
and reindexing transports the exponents to the local certificates.

Each lower exponent is its newvector conductor plus the rank times the
additive conductor. The upper exponents add under normalized induction,
and all conjugate blocks have the same newvector conductor. The count of
norm characters and the trace formula for additive conductors cancel the
lower additive conductor terms and leave the different term. The
newvector certificates identify the finite exponents in the resulting
identity with the Library's first fixed levels.

The completed-equation argument adapts Arthur–Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989), Ch. 1,
Proposition 6.9(ii), equations (6.15)–(6.17) and Lemma 6.13, printed
pp. 69–70 (PDF pp. 83–84). The literature ID is `arthur-clozel-1989-base-change`,
with SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
