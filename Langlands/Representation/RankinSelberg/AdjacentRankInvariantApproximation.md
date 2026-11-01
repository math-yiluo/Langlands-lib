# A common compact open level for full-rank approximation

This internal construction connects the full-rank cutoff tests with the actual
canonical normalized opposite-parabolic induction of ordered shape (r+1,1).
It retains the original algebraic representation space V, its independent
universe, and the lifted scalar tensor factor used by the host statement.
The only representation hypothesis is smoothness of sigma. The character chi
is an arbitrary quasicharacter. Every natural r, including zero, is allowed.

`exists_adjacentRankTestWeightLevel` starts with any rectangular Schwartz–Bruhat
test Phi and any smooth scalar character theta of GL_(r+2). The uniform open
right stabilizer of Phi is intersected with the open kernel of theta. The
compact open subgroup basis supplies a compact open subgroup J inside this
intersection. Thus J fixes Phi under actual right matrix multiplication,
and theta is one on J.

`AdjacentRankInvariantApproximationData` bundles a single compact open level J
and a sequence Psi_n of `adjacentRankCompactTests (r+1) F.Carrier`. Every Psi_n
is right J-invariant, has pointwise norm at most the norm of Phi, and eventually
equals Phi at each full-row-rank rectangular matrix. For every n and every
original vector v, the actual `adjacentRankNormalizedSection` built from Psi_n
and v belongs to the invariant submodule of the exact host induced
representation restricted to J. The same J works for all n and all v.

`nonempty_adjacentRankInvariantApproximation` proves that this data exists.
It takes theta to be the outer determinant weight
chi(det g) times |det g|^((r+1)/2) from the normalized-section formula. The
previous level construction supplies J. The invariant full-rank cutoff API
then supplies Psi_n, its norm bound and eventual full-rank equality. Equality
of the translated compact test follows from its pointwise J-invariance. The
proved `adjacentRankNormalizedSection_right` formula gives the induced action
as theta(k) times the section of the translated test. Both factors simplify
for k in J, proving membership in the actual fixed-vector submodule.

`adjacentRankInvariantApproximation` chooses such bundled data. This is a
derived construction from the existing stabilizer, compact-open subgroup basis,
full-rank cutoff and normalized-section APIs. It asserts no convergence at
rank-deficient matrices, no convergence of integrals, no finite-dimensionality
or closedness of any coefficient image, and no whole image equality. Those
analytic and representation-theoretic steps belong to the host assembly.
