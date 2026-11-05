# Canonical pairings and integration on actual discrete-series orbits

This derived construction combines Waldspurger V.2, printed p.293 / PDF p.59,
VI.1, printed pp.295–296 / PDF pp.61–62, and the orbit-measure convention of
VI.3, printed pp.301–302 / PDF pp.67–68. It uses the existing canonical
normalized product inductions, inverse formal degrees, actual inducing
transport, coherent smooth sections and actual discrete-series orbit measure.

The explicit group, semidirect decomposition, closedness, local compactness,
nonarchimedean topology, second countability, Borel structures, compact-open
factorization, ambient unimodularity and full parabolic modulus hypotheses
are those of the source-form constructions. The inducing object is an
irreducible admissible canonical smooth representation, square integrable
modulo the displayed normal central subgroup `C`. One inversion-invariant
quotient Haar measure `μ` on `M / C` determines every formal degree.
Compact-open cofinality, continuity of the positive characters and continuity
of the Levi projection remain explicit. The group, character-index,
coefficient-carrier and finite-coordinate universes remain independent.
No coefficient norm or topology, chosen positive inducing form or
irreducibility of parabolic induction is supplied.

`unitaryOrbitRepresentativeProductForm` uses the canonical inverse-degree form
at every actual inducing representative. Square integrability on the fixed
central quotient comes from the existing unitary-orbit comparison. Its
transport theorem applies `formalDegreeProductForm_ofEquiv`, preserving the
whole Hermitian form under every actual inducing equivalence. The complex
form remains antilinear in its first variable, as in V.2.

`unitaryOrbitProductPairing` chooses an actual inducing representative of
each element of the actual discrete-series class orbit. The existing
representative-to-orbit map is surjective. The representative theorem proves
that this scalar equals the source-form pairing at any representative: it
converts equality of orbit classes into an actual smooth-representation
equivalence, uses coherence of both sections and applies canonical form
transport. Thus the scalar is independent of the auxiliary representative
and equivalence. Its parameter theorem identifies it with the previously
constructed inverse-degree fiber pairing at the literal character parameter.

A finite torus group equivalence `e` is supplied, and only continuity of its
forward map is required. The scalar torus pairing is continuous because it
is the scalar-smooth pairing of the actual dependent families. Pulling back
along `e` gives a continuous character pairing. The actual twist map is an
open quotient map, so this also proves continuity on the original
stabilizer-quotient topology of the actual orbit. No inverse-continuity or
compactness assertion about the character group or actual orbit is needed.

For the integral construction, the finite quotient
`Finite (M / (commonNormKernel ν ⊔ C))` is an explicit additional premise.
The existing `finite_discreteSeriesStabilizer` derives finiteness of the
actual class stabilizer `S` from this premise. It also identifies the relevant
unitary stabilizer with the full unramified stabilizer. No finiteness of the
family of discrete-series orbits is assumed or proved here.

For a character measure `η`, `unitaryOrbitParameterMeasure` is exactly

`(Nat.card S : ℝ≥0∞)⁻¹ • Measure.map e η`.

Its total mass is `(Nat.card S : ℝ≥0∞)⁻¹ * η Set.univ`. The measure is finite
when `η` is finite: `S` is a finite nonempty subgroup, so its cardinal is
positive and the inverse scalar is finite. If `η` is positive on nonempty
open sets, continuity and surjectivity of `e` give the same property to its
pushforward, and the nonzero scalar preserves it. These statements preserve
the original character scale; they do not declare either measure to be a
probability measure.

`integral_unitaryOrbitProductPairing_eq_parameterIntegral` identifies the
integral of the descended scalar over the actual orbit, against the existing
`discreteSeriesOrbitMeasure`, with the fiber integral on this scaled torus
cover. It expands both measures, applies the Bochner scalar-measure and
measurable-pushforward identities, then uses the parameter theorem pointwise.
Continuity gives strong measurability of both scalar functions. The identity
itself does not require a finite character measure.

`integrable_unitaryOrbitProductPairing` separately proves actual convergence
when `η` is finite. The continuous scalar torus pairing is bounded by
compactness of the finite torus. Its bounded continuous pullback along `e`
is integrable against `η`; pushforward and multiplication by the finite
inverse stabilizer cardinal give integrability against the actual orbit
measure. Thus the integral identity does not conceal a convergence input.

`productInducedSmoothOrbitCore` additionally requires `η` to be positive on
nonempty open sets. It is the existing positive coherent-section cover core
with precisely `unitaryOrbitParameterMeasure`. Definiteness follows from
that core's proved finite scalar-smooth positivity and faithful pullback.
`productInducedSmoothOrbitCore_inner_integral` proves that its entire
Hermitian form is the convergent actual-orbit integral of
`unitaryOrbitProductPairing`. The final tensor theorem applies the existing
concrete tensor-to-section isometry with the same scaled cover measure. It
retains the genuine, possibly nontrivial stabilizer coefficient action;
no trivial coefficient action or replacement section space is introduced.

When the supplied character measure is also left invariant, the existing
`isLocallyMeasurePreserving_discreteSeriesOrbitMap` proves that this exact
orbit measure satisfies VI.3's local-preservation convention. The present
construction needs no invariance hypothesis for convergence or definiteness.
It does not construct the I.1 character scale on all rational-point inputs,
the spectral density, density-weighted or global spectral forms, full group
action invariance, arbitrary coordinate independence, wave packets, Hilbert
completions, or a Plancherel isometry. All whole-task obligations remain open.
