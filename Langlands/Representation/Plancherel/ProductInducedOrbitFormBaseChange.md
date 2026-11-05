# Base-object independence of actual orbit pairings and cores

This derived construction combines Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d’après Harish-Chandra)*, V.2 (printed p.293,
PDF p.59), VI.1 (printed pp.295–296, PDF pp.61–62), and VI.3 (printed p.302,
PDF p.68). The source defines the inverse-formal-degree Hermitian form,
coherent sections on actual inducing representatives, and the measure locally
preserved by the unitary-character orbit map. The present pair proves that
the implemented scalar pairing and positive integral core are independent
of the actual representative used to center that same orbit. It imports the
existing actual section equivalence, canonical forms and orbit measures.

The initial comparison uses a nonarchimedean topological group, an actual
subgroup `M`, indexed positive characters `ν`, a canonical irreducible
admissible smooth complex representation `π`, and an actual representative
`A` in its unitary unramified twist orbit. The square-integrability premise
uses one fixed normal central subgroup `C` and one fixed quotient Haar
measure `μ`. Every new-base square-integrability proof is derived from
unitary twisting on this same quotient.

`unitaryOrbitDiscreteSeriesBaseHomeomorph` is the identity on actual
discrete-series classes from the orbit centered at `A` to that centered at
`π`. Its underlying equivalence changes only orbit-membership proofs.
Membership of `A` gives a character `χ` with `χ • [π] = [A]`; the orbit sets
then agree by the group-action orbit identity. Continuity in each direction
is proved with the existing open quotient character maps: the new-base map
is the old one precomposed with translation by `χ`, and the inverse uses
translation by `χ⁻¹`. Thus both original stabilizer-quotient topologies are
respected. No topology on the entire smooth dual is required. The two value
lemmas state that each direction retains the actual class.

`unitaryOrbitDiscreteSeriesStabilizer_eq` rewrites the new base as a unitary
twist and uses the existing commutative-action stabilizer theorem. The
subgroups are equal, not merely equicardinal. The representative-map square
`unitaryOrbitRepresentativeDiscreteSeriesOrbit_baseChange` is equality of
classes after the existing representative reindexing.

`map_unitaryOrbitDiscreteSeriesBaseHomeomorph_measure` explicitly requires
finite stabilizers at both bases and left invariance of the supplied unitary
character measure `η`. It proves that the homeomorphism pushes the new-base
orbit measure to the old-base orbit measure. The proof expands the existing
inverse-cardinality pushforward, composes its two measurable maps, and
cancels character translation by left invariance. Equality of the actual
stabilizers identifies the two inverse-cardinality factors. The scale of
`η` is retained throughout; no probability normalization is imposed.

For the product-induced pairing, the additional premises are exactly the
existing source-form and smooth-section hypotheses: local compactness,
second countability and Borel structures, the actual semidirect decomposition
`P = M U`, closed `P` and `U`, compact open `K` and `G = P K`, ambient
unimodularity, the full parabolic modulus identity, compact-open cofinality,
inversion invariance of `μ`, continuous positive characters and Levi
projection, and supplied finite torus group coordinates `e`. No coefficient
norm or topology or positive inducing form is supplied. The group,
character-index, coefficient-carrier and coordinate universes are independent.

`unitaryOrbitProductPairing_baseChange` proves pointwise preservation by the
existing `productInducedSmoothOrbitBaseEquiv`. Surjectivity of the actual
representative map reduces the equality to one actual inducing object.
The representative-map square and the previously proved scalar descent
theorem identify both sides with the same canonical form on the same
fiber values. Different square-integrability witnesses have no effect.
This pointwise statement requires no finite quotient, measure invariance,
or continuity of `e`.

For the integral and core statements the additional finite central norm
quotient `Finite (M / (commonNormKernel ν ⊔ C))` derives both actual
stabilizer-finiteness instances by the existing theorem.
`unitaryOrbitParameterMeasure_baseChange` proves equality of the two
source-scaled torus-cover measures directly from stabilizer equality. It
needs no invariance of `η`.

`integral_unitaryOrbitProductPairing_baseChange` also requires continuity
of the forward coordinate map `e` and left invariance of `η`. It rewrites
the old orbit measure as the proved pushforward, applies the Bochner
pushforward identity to the continuous descended scalar pairing, and uses
the pointwise base-change theorem. The identity itself permits arbitrary
mass. When `η` is finite, the previously proved
`integrable_unitaryOrbitProductPairing` supplies actual Bochner convergence
at both bases.

Finally, `productInducedSmoothOrbitBaseEquiv_inner` assumes that `η` is
finite and positive on nonempty open sets, in addition to left invariance.
It identifies each entire positive core with its convergent actual-orbit
integral and applies the integral comparison. The existing linear
equivalence therefore preserves the whole Hermitian form. Its underlying
actual section values, the coefficient action of self-twists and the
inverse actual stabilizer-cardinality normalization are retained.

This is conditional independence of the base inducing representative for
one actual orbit with the same supplied coordinates and measures. The
rational-point realization of the I.1 character scale, arbitrary coordinate
independence, spectral density, density-weighted global forms, full action
invariance, wave packets, completions and Plancherel inversion remain
separate obligations. No whole-task completion condition is claimed.
