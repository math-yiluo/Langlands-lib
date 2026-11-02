# Derived compact complexes and hyperext on actual induced rational spectra

Author: Worker 13.

This module applies the existing derived-complex and hyperext constructions to
the full locally constant smooth sheaf on the actual induced rational spectrum.
It constructs the derived object itself, identifies its cohomology naturally
with the existing sheaf-derived compact sections, and describes the second page
of its hyperext spectral sequence.

## Setting

`K : Type u` is a complete ultrametric normed field,
`P : PresentedStrictAffinoidAlgebra K`, and `ρ` is a rational spectral action
of a topological group `G : Type u` on `P`. For
`X : ρ.OpenSubgroupTransport`, `X.InducedSpectrum` is the constructed balanced
quotient of `G` times the Banach spectrum of its rational quotient algebra.
Its topology and jointly continuous action are the existing induced-space
constructions.

The coefficient ring `R : Type u` is commutative. Coefficients are arbitrary
objects of `SmoothRep.{u, u, u} R G`; no coefficient topology, finite-dimensionality
or triviality of the group action is required. The spatial hypothesis
`HasStableNeighbourhoods G X.InducedSpectrum` remains explicit.

The module assumes independently
`HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X.InducedSpectrum)` and
`HasDerivedCategory.{w'} (SmoothRep.{u, u, u} R G)`.
No derived-category instance or relationship between `w` and `w'` is chosen.
The hyperext page objects belong to `AddCommGrpCat.{w'}`.

## The actual derived compact complex

All names below lie in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SmoothCohomology`.

`compactDerivedComplex X` is `sheafFunctor X` followed by
`SmoothSheafDerivedComplex.compactComplex R G X.InducedSpectrum`. Thus it
sends each coefficient representation to the bounded below derived smooth
representation obtained by applying the derived compact-section functor to its
full locally constant smooth sheaf. The sheaf and all its coefficient maps are
the ones already constructed in `InducedRationalSmoothCohomology`.

For `q : ℕ`, `compactDerivedComplexHomologyIso X q` is the natural isomorphism
from the degree-`q` cohomology of that derived complex to `compactDerived X q`.
It is obtained by whiskering `DerivedPlus.homologyNatIso` with the sheaf
coefficient functor. In particular, its naturality concerns every original
smooth coefficient intertwiner.

For any coefficient `M` and any injective resolution `I` of
`(sheafFunctor X).obj M` in the smooth sheaf category,
`compactDerivedComplexIso X M I` identifies the constructed derived complex
with the derived image of compact sections applied termwise to `I`, after
extending its nonnegative cochain complex by zero to integer degrees.
`compactDerivedComplexHomologyIso_hom_app` identifies the component of the
natural cohomology isomorphism with `DerivedPlus.homologyIso` computed using
that same arbitrary resolution.

`isZero_compactDerivedComplex_homology` proves vanishing in every negative
integer degree using the existing vanishing theorem for derived compact
sections. `compactDerivedComplexHomologyZeroIso` composes the degree-zero
cohomology comparison with `compactDerivedZeroIso`. Its target is exactly
`CompactSections.coefficientFunctor X`: all compactly supported locally
constant functions with the original diagonal action
`(g · f)(z) = g · f(g⁻¹ · z)` and the original pointwise coefficient maps.

`compactDerivedObject X` includes this constructed complex into the unbounded
derived category by `DerivedCategory.Plus.ι`.
`compactDerivedObjectHomologyIso X q` retains the same natural cohomology
identification; bounded below homology is definitionally the inclusion followed
by unbounded homology.

## Hyperext of the constructed object

For smooth coefficient representations `M` and `W`,
`compactHyperextSpectralSequence X M W` is the existing standard-t-structure
hyperext spectral sequence with first argument
`(compactDerivedObject X).obj M` and second argument `W` placed in degree zero.
Its first argument is therefore constructed from the actual sheaf above.

For `p q : ℕ`, `compactHyperextSecondPageAddEquiv X M W p q` identifies
the abelian group at position `(p, -q)` on page two with
`(SmoothExt.ext R G ((compactDerived X q).obj M) p).obj W`.
Here smooth Ext is the `p`-th right derived functor of equivariant Hom in
the abelian category of smooth representations. The construction uses
`SmoothHyperext.secondPageAddEquiv` at integer index `-q`, rewrites
`-(-q) = q`, and transports its first Ext argument along
`compactDerivedObjectHomologyIso X q`. Because Ext is contravariant in
that argument, the transported map uses the opposite of the inverse
cohomology isomorphism.

`compactHyperextSecondPageZeroRowAddEquiv` sets `q = 0` and transports
through `compactDerivedZeroIso`, identifying position `(p, 0)` with
smooth `Extᵖ` from the original full compact-function representation to `W`.
`compactHyperextSecondPageZeroColumnAddEquiv` sets `p = 0` and uses
`SmoothExt.extZeroIso`, identifying position `(0, -q)` with the group of
actual smooth equivariant maps from `(compactDerived X q).obj M` to `W`.
These are additive equivalences; no scalar linearity or naturality of the
hyperext equivalences is asserted.

## Provenance and scope

This is an internal specialization and composition of existing constructions.
`InducedRationalSmoothCohomology` supplies the full smooth sheaf and the actual
sheaf-derived compact-section functors, including their degree-zero compact
function identification. `SmoothSheafDerivedComplex`, `DerivedPlus` and
`DerivedPlusNaturality` supply the derived complex, its arbitrary-resolution
representation and natural cohomology comparison.
`SmoothHyperextSecondPage` supplies the additive hyperext identification;
`SmoothExt.bifunctor` and `extZeroIso` supply the subsequent transports.
The implemented proofs apply these results and rewrite the double negation in
the cohomology index. No new assertion from the original literature is claimed.

The sheaves here use ordinary opens on the actual induced spectrum. The
construction evaluates the derived compact-section functor in the smooth
sheaf category; it does not assert that the composite coefficient functor
itself is derived. It asserts no higher Godement comparison, acyclicity of a
particular resolution, analytic/étale comparison, spectral-sequence convergence,
arithmetic tower, uniformization or Harris specialization. These remain
separate construction or theorem obligations under the broader task.
