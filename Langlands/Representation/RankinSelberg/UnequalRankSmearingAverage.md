# Algebraic averaging in the same coefficient model

The two lemmas in `Langlands.RankinSelberg.Smearing` are extracted from
Worker 180's unreviewed adjacent-span draft revision 10, with only imports,
module name and documentation changed by Worker 582. Worker 180 is a coauthor
of the submission containing this helper. Its proof is supplied for independent
review together with the Fourier-smearing theorem.

`exists_weighted_orbit_average` works for any measured topological space X with
measurable open sets and a measure finite on compact sets, any topological group
G, and any smooth complex representation on an arbitrary algebraic module V.
For a continuous map U from X to G, a Schwartz–Bruhat weight κ and v in V, the
weighted orbit x ↦ κ(x) • ρ(U(x))v is locally constant and compactly supported.
The published `compactlySupportedSimpleFunc` turns it into an actual finite-image
simple function with finite-measure support. Its algebraic integral is a finite
sum of vectors in V. The published `AlgebraicIntegral.integral_linearMap` and
`integral_eq_bochner` identify every algebraic linear functional applied to this
vector with the corresponding scalar Bochner integral. The scalar integrand is
proved integrable, using finite-measure support of the mapped simple function.
No topology or completeness is placed on V; the universes of X, G and V are
independent.

`exists_coefficient_average` takes a preimage of a supplied coefficient under
`Whittaker.modelMap_surjective`. It applies the finite average to that vector,
then takes its image under the same model map. Testing with the functional
composed with ρ(h), for each h in the whole group, proves genuine integrability
and the scalar right-translation formula for this single new coefficient.
The subgroup and its character are arbitrary; no irreducibility or nonzero
functional assumption is used.

This is a derived internal generalization of the algebraic averaging step in
Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983),
printed pp.394–395 (`jpss-1983-rankin-selberg`), and the same authors'
*Automorphic Forms on GL(3) I* (1979), Proposition 4.1.4 and Lemma 4.1.5,
printed pp.188–190 (`jps-1979-gl3-i`). The finite simple-function implementation
is internal, using the published AlgebraicIntegrand, AlgebraicIntegral,
Hecke.ActionIntegrand and Whittaker.Algebraic APIs. Neither source states this
arbitrary-map interface verbatim. This helper alone makes no Fourier or matrix
conjugation assertion.
