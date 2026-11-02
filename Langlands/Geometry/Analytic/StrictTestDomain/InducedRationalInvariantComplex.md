# Invariant compact complexes on actual induced rational spectra

Author: Worker 13.

This pair applies the existing invariant compact-section constructions to the
full locally constant smooth sheaf on the actual balanced rational spectrum.
It constructs the Godement complex, sheaf-derived invariant compact sections
and a bounded-below derived complex of modules. Their degree-zero
identifications retain the invariants of the original full compact-function
representation, naturally in all smooth coefficient intertwiners.

## Setting

The namespace is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SmoothCohomology`.
The field `K`, group `G`, commutative coefficient ring `R` and smooth module
carriers share universe `u`. The field is complete and ultrametric, and `G` is
a topological group. Given a rational spectral action on a presented strict
affinoid algebra, `X` is an `OpenSubgroupTransport`. Its `InducedSpectrum` is
the constructed balanced quotient of the rational quotient Banach spectrum,
with its jointly continuous group action.

`HasStableNeighbourhoods G X.InducedSpectrum` is an explicit spatial
hypothesis. Coefficients range over all objects of `SmoothRep.{u,u,u} R G`,
without a coefficient topology or finite-dimensionality assumption.
`sheafFunctor X` is the existing full ordinary-open locally constant smooth
sheaf functor. It retains every original locally constant section and every
coefficient map.

Only the bounded-below derived-complex section assumes
`HasDerivedCategory.{w}` for the smooth sheaf category and
`HasDerivedCategory.{w'}` for `ModuleCat.{u} R`. These two localization
universes are independent. No derived category of smooth representations is
needed by this pair.

## Invariant compact functions and Godement sections

`invariantCompactFunctions X` is the original full compact-function
coefficient functor followed by the existing `smoothInvariants R G`. Thus
its carrier at `M` consists of compactly supported locally constant functions
fixed by every element of `G`, under the original diagonal action
`(g.f)(z) = g.(f(g⁻¹.z))`. Its maps are the restrictions of the original
pointwise coefficient intertwiners.

`invariantCompactSectionsIso` applies the invariants functor to the existing
full `compactSectionsIso`. Its source is `invariantCompactFunctions X`,
and its target is the constructed sheaf followed by actual invariant compact
sections. The equality of invariant compact sections with compact sections
followed by smooth invariants is definitional in the imported API.

`godementInvariantCompactComplex` evaluates the existing
`smoothGodementInvariantCompactComplex` on `sheafFunctor X`. This takes
invariant compact sections termwise on the actual smooth Godement complex,
which is constructed by iterated cokernels of its monic coaugmentation.
`godementInvariantCompactCohomology X q` is its categorical degree-`q`
homology in `ModuleCat R`.

`godementInvariantCompactCohomologyZeroIso` first uses the general
monic-coaugmentation degree-zero theorem, then the inverse of
`invariantCompactSectionsIso`. It identifies degree-zero homology with
all invariant compact functions. It requires no higher acyclicity or
Godement resolution comparison theorem.

## Sheaf-derived invariant sections

`invariantCompactDerived X q` evaluates
`SmoothSheafCohomology.invariantCompactDerived` on the constructed full
coefficient sheaf. The right derived functor is taken in the abelian
category of smooth sheaves, using its existing enough-injectives instance.
It derives the composite invariant compact-section functor on that sheaf
category.

`invariantCompactDerivedZeroIso` identifies degree zero with full
invariant compact functions by the left-exact degree-zero theorem followed
by `invariantCompactSectionsIso.symm`.
`invariantCompactDerivedIso M I q` computes the derived value as the
homology of invariant compact sections of any injective resolution `I`
of `(sheafFunctor X).obj M`.

`godementInvariantDerivedZeroIso` composes the Godement-to-functions
isomorphism with the inverse of the derived-to-functions isomorphism.
Its compatibility equation
`godementInvariantDerivedZeroIso_hom_comp` says that this map followed by
the derived-to-functions map is the original Godement-to-functions map.
The implemented proof uses associativity and the isomorphism inverse laws.

## Canonical maps to invariants of compact cohomology

`godementInvariantsEdge X q` is the natural map
from homology of termwise invariant compact Godement sections to
invariants of `godementCompactCohomology X q`.
`derivedInvariantsEdge X q` is the natural map from
`invariantCompactDerived X q` to invariants of `compactDerived X q`.
Both are obtained by left-whiskering the existing
`SmoothGodementComparison.godementEdge` and `derivedEdge` with the actual
`sheafFunctor X`. They require no quasi-isomorphism hypothesis for the
Godement augmentation.

These maps use the left exactness of invariants. For a complex, invariants
preserve its cycles; the inverse of the induced cycles isomorphism,
followed by invariants of the homology projection, kills boundaries and
descends to homology. The derived edge applies this map to compact
sections of an injective resolution, between the two derived-functor
resolution isomorphisms. `derivedInvariantsEdge_app` identifies its
component with this construction for every injective resolution of the
actual coefficient sheaf, by the existing resolution-independence theorem.

Both edges are isomorphisms in degree zero. Under the explicit extra
hypothesis that `smoothInvariants R G` preserves homology, both are
isomorphisms in every nonnegative degree. These instances reuse the
corresponding generic instances and the preservation of isomorphisms by
whiskering. This pair does not prove that extra hypothesis for any group
or coefficient ring.

## The actual bounded-below derived complex

`invariantCompactDerivedComplex` composes `sheafFunctor X` with
`SmoothSheafDerivedComplex.invariantCompactComplex`. The latter places
the sheaf in degree zero and applies the actual bounded-below right
derived functor of invariant compact sections.

`invariantCompactDerivedComplexHomologyIso X q` is a natural
isomorphism from its degree-`q` homology to
`invariantCompactDerived X q`. It left-whiskers
`DerivedPlus.homologyNatIso`, retaining naturality for every coefficient
intertwiner.

`invariantCompactDerivedComplexIso M I` represents this derived object
by invariant compact sections applied to any injective resolution of
the constructed sheaf, extended by zero to integer degrees.
`invariantCompactDerivedComplexHomologyIso_hom_app` identifies the same
natural homology comparison with `DerivedPlus.homologyIso` computed using
that arbitrary resolution. It directly applies the existing
resolution-independent component theorem.

`isZero_invariantCompactDerivedComplex_homology` proves categorical
vanishing in every negative integer degree by specializing the existing
negative-vanishing theorem. The injective resolution has nonnegative
degrees and is extended by zero. No upper bound is asserted.

`invariantCompactDerivedComplexHomologyZeroIso` composes the natural
homology comparison at zero with `invariantCompactDerivedZeroIso`, giving
all invariant compact functions.
`invariantCompactDerivedComplexEdge` composes the homology comparison
with `derivedInvariantsEdge`, producing a natural map from the homology
of this actual derived object to invariants of the actual compact
cohomology. It is an isomorphism at zero and, under the explicit
preservation-of-homology hypothesis, in every nonnegative degree.

## Provenance and scope

Provenance is internal specialization and composition of the existing
actual induced-spectrum, full locally constant smooth sheaf, full compact
function comparison, Godement, derived-functor and left-exact-homology
constructions. No new assertion from original literature is claimed.
The generic APIs retain their role for arbitrary smooth sheaves and
arbitrary left exact functors; this pair fixes the constructed geometric
space and full coefficient sheaf and supplies their full function
identifications.

This pair evaluates sheaf-derived functors on the constructed coefficient
sheaf. It does not assert that they are the right derived functors of
the coefficient-level composite. The maps to invariants of compact
cohomology are constructed, with isomorphism assertions under precisely
the conditions stated above. Positive-degree isomorphisms for these
edge maps require the preservation-of-homology hypothesis in this pair.

Higher comparison between Godement and sheaf-derived constructions,
acyclicity of Godement terms, analytic or etale site identification,
subgroup-level or quotient-group variants, spectral sequence convergence,
arithmetic towers, uniformization and Harris specialization remain
separate obligations.
