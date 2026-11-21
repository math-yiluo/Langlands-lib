# Opposite Weyl characters in spherical trace replacement

`weylSphericalTraceReplacement` proves `WeylSphericalTraceReplacementStatement`.
It takes two finite families of inducing tuples, Jacquet exponent multisets,
and elementary and spherical traces. Tuples consist of nonzero complex
uniformizer values. A common finite label type embeds in `Eigenvalues n`, the
Library type of unordered parameters with multiplicities. The extension label
uses the inducing tuple's unordered values. The base label uses the same
construction after raising the values to the positive degree `l`.

`HasWeylJacquetSupport` requires each exponent multiset to lie in the full
Weyl multiset of the inducing tuple. The full multiset is indexed by
permutations, including those that give equal tuples. Spherical contributors
have this full multiset. The other contributors omit every tuple whose
complex absolute values are weakly decreasing. These are the tuples in the
opposite order to the Langlands order by weakly increasing absolute values.

`HasJacquetElementaryTraceExpansion` gives each elementary trace as a sum
over its Jacquet multiset times a common factor. The factor is nonzero on
every strictly decreasing weight. The extension sum evaluates at the
weight itself and the base sum evaluates at `l` times the weight.
`HasSphericalTraceValues` gives a common spherical trace value for each label
on paired tests, and zero trace on contributors without spherical vectors.
The input identity is equality of the weighted elementary trace sums at
every strict weight. The conclusion is equality of the weighted spherical
trace sums on every paired test.

The implementation sends a tuple to the lattice character given by the
product of its coordinate powers. Evaluation on coordinate basis vectors
proves injectivity. Multiplication of all weights by `l` is equivalent to
raising the tuple to that power. Mapping the multiset first and then counting
characters gives the finite character sum used in
`sphericalTraceReplacementReduction`.

For each label, the proof sorts a representative of the corresponding
unordered spectrum by decreasing absolute value and selects its character.
The full Weyl multiset depends only on the unordered spectrum. The proof
reindexes equal spectra by matching the finite fibres of each complex
value, and reindexes the full multiset by left multiplication on the
permutation group. Taking coordinatewise powers commutes with permuting
coordinates. For a spherical contributor with the given label, the selected
character has the positive multiplicity it has in that common full multiset.
If an exponent contributes to the selected coefficient, the Weyl support
forces its powered spectrum to have the same label. A positive power
reflects the order of the coordinate absolute values, so the original
exponent was already in opposite order. The exclusion premise then forces
the contributor to be spherical. This verifies `DetectsSphericalContributors`
on both sides, and the finite spectral reduction gives the trace equality.

This internal reduction formalizes the use of the full Weyl multiset,
opposite characters, and norm pullback in Henniart–Lemaire,
*Changement de base et induction automorphe pour* `GL_n` *en
caractéristique non nulle*, I.5.4 through I.5.5, printed pp. 34–39
(PDF pp. 42–47). The actual Jacquet expansions, the support and exclusion
properties for irreducible generic constituents, and the spherical trace
evaluations enter as premises.
