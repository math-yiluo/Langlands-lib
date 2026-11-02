# Fixed-rank affine direct images

The module supplies two parts of the sheaf endpoint for the ordinary direct-image problem.
All coefficient sheaves are actual module sheaves, and all pullbacks, direct images and
scalar comparisons are the existing specified constructions.

`isPullback_principalOpenBaseChange` proves that the square underlying
`principalOpenBaseChangeSquare` is Cartesian. It flips the restriction pullback square
and transports its open base through `basicOpenIsoSpecAway`. Consequently,
`isQuasicoherent_pushforward_of_affineScalarBaseChange` deduces quasi-coherence of
`f_* M` from invertibility of the specified scalar sections comparison for every
Cartesian affine base change of `f : X → Spec R`. It applies the existing
principal-open quasi-coherence criterion. There is no finiteness hypothesis in this part.

`exists_freeNeighborhood_of_finite_projective_rankAtStalk` concerns a quasi-coherent
module sheaf `P` on `Spec R`. Suppose its actual global-sections module `N` is finite
and projective, and `Module.rankAtStalk N q = n` at every prime. At each point it
constructs an open neighborhood on which the restriction of `P` is isomorphic to the
free sheaf on `ULift (Fin n)`. The point's localized module is free by finite flatness
over its local ring. Its prescribed rank gives a basis with exactly that index type.
Finite projective implies finitely presented, so Mathlib's
`Module.FinitePresentation.exists_basis_localizedModule_powers` lifts that basis to
some principal-open localization avoiding the point's prime. The localized-module
tensor equivalence transports this basis to scalar extension. The definition
`freeChartOfLocalizedBasis` then converts such a basis into the actual free chart.
The tilde pullback
isomorphism and `tildeFinsupp` then give a free chart on the localization spectrum.
Restriction through `basicOpenIsoSpecAway` gives the asserted chart on the open.
This argument also covers rank zero and makes no nonemptiness assumption on `Spec R`.

`isLocallyFreeOfRank_of_finite_projective_rankAtStalk` packages these neighborhoods
using `isLocallyFreeOfRank_of_freeNeighborhoods`. Its conclusion is the actual
`Langlands.Scheme.Modules.IsLocallyFreeOfRank P n`, with the specified finite
number of generators in every chosen local basis.

These are internal derived consequences of the published restriction, tilde,
scalar-base-change and fixed-rank APIs and Mathlib's module localization results.
They do not establish the finite-projective or scalar-comparison hypotheses and
do not yet globalize the canonical sheaf comparison to arbitrary base schemes.
