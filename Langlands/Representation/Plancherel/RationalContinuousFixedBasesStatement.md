# Continuous finite fixed matrices for actual rational induction

`RationalNormalized.RationalContinuousFixedBasesStatement` is an internal
derived target for the existing full normalized rational induced family
`complexInduced`. It works over arbitrary nonarchimedean local fields and
connected reductive group schemes, with independent field and representation
carrier universes. It uses all the rational norm characters in the existing
`parabolicLeviRationalNormCharacters` family and the full complex unramified
character topology.

The hypotheses specify an actual parabolic root presentation, its actual
semidirect decomposition on rational points, closedness of the actual
unipotent image, continuity of the semidirect projection, compactness of the
literal left parabolic quotient and admissibility of the inducing smooth
complex representation. The ambient rational points have their rational
point topology with locally compact and nonarchimedean group structures.
A Borel measurable structure and a left Haar measure are supplied.

For every compact open subgroup `K`, the proposition asserts a natural number
`d` and a basis indexed by `Fin d` of the actual `K`-fixed space in every
unramified fiber. For every ambient group element and every pair of indices,
the entry of the actual normalized Hecke-compressed matrix in these bases
is a continuous function of the character. The bases themselves are purely
algebraic data; no topology on their varying carrier spaces is claimed.
The value `d = 0` is allowed.

This target is derived from the published finite-free universal compact-fixed
modules, actual full-induced specialization and regular-function continuity.
These results suggest extending a universal coefficient basis to each complex
fiber and using the evaluated coefficient formula for the actual Hecke
matrices. This statement does not itself prove the target.

The family uses positive full-parabolic normalization. Comparison with
positive Levi normalization, uniform detection of all irreducible
subquotients, nonzero fibers and an irreducible parameter remain separate
obligations for the host generic irreducibility theorem. No such input is
added to the host statement here.
