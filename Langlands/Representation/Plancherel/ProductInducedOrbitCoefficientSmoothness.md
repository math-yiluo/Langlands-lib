# Smoothness and orbit continuity of the actual coefficient

Worker 200. This derived construction proves the finite-torus parameter form
of Waldspurger Lemma VI.2.1(i), printed p.296/PDF p.62: for a coherent smooth
orbit section and fixed `g`, its actual induced coefficient is smooth in the
orbit parameter. It also proves continuity for the actual quotient topology on
the discrete-series orbit. The coefficient is the existing actual descended
map of V.1, printed p.288/PDF p.54, on the section space of VI.1, printed
pp.295–296/PDF pp.61–62. Registered source: `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The implemented proof uses a fixed compact linear functional and full action
stability; it is an internal proof route through those actual objects.

## Explicit setting

All subgroup, topological, normalization and representation premises of
`ProductInducedOrbitCoefficients` remain displayed: locally compact,
nonarchimedean, second countable Hausdorff `G` with its Borel structure;
actual semidirect `P = M U`, closed `P` and `U`, locally compact `P`, a fixed
compact open `K` and actual `G = P K` factorization; ambient unimodularity and
the full parabolic modulus identity; continuous norm characters and Levi
projection; and a canonical irreducible admissible complex inducing object.
Its carrier has no imposed topology, norm or finite dimension. Group,
character-index, inducing-carrier and finite parameter-index universes are
independent.

The actual discrete-series orbit uses a fixed prescribed central quotient and
its Haar measure with square-integrability of the inducing object. No extra
Borel structure, inversion invariance, finite central norm quotient,
compact-open cofinality or positive inducing form is used here. The generic
finite-torus coordinates satisfy the algebraic
`HasLaurentUnitaryCoordinates` condition, whose evaluation smoothness is proved
in the scalar prerequisite and whose canonical rational case is verified
there. Full smooth-section stability is the separate proved construction;
it is not a premise standing in for this conclusion. Rational parabolic
realization is not established by this generic module.

For the final orbit-continuity theorem only, the forward coordinate map `e`
is continuous. No inverse-coordinate continuity is assumed. Smoothness of the
parameter pullback itself needs no coordinate-continuity premise.

## A fixed linear functional at the identity

`productInducedCompactCoefficientAtOne` is a linear functional on the existing
untwisted compact-picture space. It extends a compact function by the actual
normalized compact equivalence, applies the existing compact-probability
coefficient map of the inducing object, and evaluates that coefficient at the
identity. The functional is constructed by composing these actual linear maps.
There is no arbitrary choice of a functional, pairing or integration scale.

The helper compact equivalence is literal restriction to `K × K`. Its inverse
evaluation theorem follows by applying restriction to its inverse and cancelling
the equivalence. The theorem `productInducedCompactCoefficientAtOne_twist`
then compares every actual unramified-twisted fiber coefficient at the identity
with this same fixed functional on its compact restriction. Both coefficients
are rewritten as the published convergent compact diagonal integrals. At a
compact diagonal point `(k,k)`, removing the actual vector and smooth-dual twists
preserves the scalar tensor contraction. This is the existing all-tensor
pairing identity for `productCompactTwistTensorEquiv`, so the integrands agree.
Integration proves the equality without a chosen tensor expansion or any
postulated identity for integrals. This step even allows nonunitary unramified
twists when the stated admissibility is supplied.

`unitaryOrbitRepresentativeCoefficientMap_at_one` specializes that identity
to the literal parameter representatives and the actual family restriction.
Thus the same functional works at every parameter, with the original compact
Haar probability and induced-duality normalization unchanged.

## Smoothness at every fixed group point

The private scalar lemma proves that a complex-valued finite scalar-smooth
family is a smooth torus function: use its actual finite expansion, pull back
to real angles, multiply each smooth scalar lift by its constant complex
coefficient, and sum the finitely many smooth functions.

For fixed `g`, translate the entire section by `(g,1)` in the already proved
full representation. That translated section still lies in the original
finite scalar-smooth section submodule. The actual coefficient action formula
identifies its coefficient at the identity with the original coefficient at
`g`, preserving the source's right-translation convention. The parameter
comparison and identity-evaluation theorem express this coefficient as the
fixed compact functional applied to the translated compact restriction.

A fixed linear map preserves the existing finite-sum family condition, so this
is a finite scalar-smooth complex-valued family. The private scalar lemma
proves `isSmoothFiniteTorusFunction_unitaryOrbitCoefficient`.
`unitaryOrbitCoefficientTorusSmoothFunction` then constructs that very actual
parameter-pulled-back coefficient as an element of the existing scalar smooth
function algebra. No differentiation under a parameter-dependent integral or
unproved coefficient estimate is used.

## Continuity on the actual orbit

`continuous_unitaryOrbitCoefficient` concerns the actual
`discreteSeriesOrbit` quotient topology, at every fixed `g`. Parameter smoothness
first gives continuity of the finite-torus pullback. Composing it with the
continuous forward coordinate map `e` gives continuity on the actual unitary
unramified character group: `e.symm (e χ) = χ` cancels algebraically. The
existing `discreteSeriesOrbitMap` is an open quotient map, so its quotient
continuity criterion descends this continuity to the orbit.

This argument requires neither inverse-coordinate continuity nor a finite
stabilizer, compactness of the whole character group, an orbit measure, or a
topology on the inducing carrier. It gives the scalar orbit-continuity
interface used by the central Fourier consumer without assuming that analytic
consumer's conclusions.

## Remaining scope

This unit proves fixed-group-point parameter smoothness and orbit continuity
for the original descended coefficient and its fixed normalization. It proves
no constant-term smoothness from VI.2.1(ii), parameter-space topology or
continuity of the coefficient map as an operator, Schwartz bound, wave-packet
convergence, weighted synthesis, Fourier transform, inversion or Plancherel
surjectivity. Those representation and analysis obligations remain separate.
