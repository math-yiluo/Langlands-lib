# Equivariant diagrams of invariant represented domains

Authors: Worker 56 and Worker 36.

## Setting and full bounded-map compatibility

Let `K : Type u` be a complete ultrametric normed field, let
`P : PresentedAffinoidAlgebra K` be an actual positive-polyradius affinoid
quotient, and let `G : Type v` be a topological group. Fix a continuous
represented-domain spectral action `ρ : DomainSpectralAction G P`.
Its continuity concerns the constructed finite-test topology on actual
bounded algebra automorphisms. All declarations lie in the namespace
`PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction`.

The imported full domain representation has already constructed the
bounded section action of the open subgroup preserving each represented
locus. `sectionAction_comp_baseMap` expresses its base equation as equality
of full bounded maps. `sectionAction_restriction` proves that the actual
restriction between two domain representations commutes with their section
actions whenever the same element of `G` preserves both loci.

This equality uses the imported full-map restriction theorem. That theorem
compares the maps after composition with the larger domain's structural
map, and the full domain universal property proves their equality.
No separation of algebra elements by spectrum points is used.
`spectrumMap_smul` also exposes equivariance of the structural spectrum map
for the inverse-pullback point actions.

## A common open subgroup and its section actions

For an open subgroup `H` of `G`, `invariantDomainProperty H` is the property
that every element of `H` preserves the actual represented locus.
`InvariantDomain H` is the corresponding full subcategory of
`Domain K P`. Its arrows remain all actual bounded restrictions over `P`;
no choice of a new restriction is imposed by equivariance.

`invariantStabilizerInclusion H d` is the continuous group homomorphism
from `H` to the domain's open locus stabilizer, sending an element to that
same element with its stabilizer proof. It is continuous as a map of
subspaces of `G`.

`invariantSectionAction H d` restricts the previously constructed bounded
section action along this homomorphism. `invariantSectionAction_baseMap`
exposes its formula on the base algebra. `invariantSectionAction_restriction`
proves full bounded-map equivariance of every retained domain restriction.
The section algebra and every bounded inverse remain the actual ones
constructed from the supplied domain representation.

## Geometric affinoid actions and actual spectra

`invariantAffinoidAction H d` is an object of
`Action (PresentedAffinoidSpace K) H`. Its underlying geometric affinoid
object is the opposite of the specified section algebra. Its map for `g`
is the opposite of the inverse bounded section automorphism.
Inversion together with passage to the opposite category gives the left
group action law.

`invariantAffinoidActionFunctor H` sends each invariant represented domain
to this action and each inclusion to the opposite of its actual bounded
restriction. The arrow equivariance follows from full-map restriction
compatibility at `g⁻¹`. The functor laws retain the identity and composite
bounded restrictions literally.

`invariantAffinoidActionFunctor_forget` states that forgetting the actions
recovers the published `Domain.toAffinoidSpace` diagram after the full
inclusion of invariant domains.

`invariantSpectrumActionFunctor H` composes this action diagram with the
existing `affinoidSpectrumFunctor` lifted by Mathlib's `Functor.mapAction`.
Thus its spaces are exactly the bounded multiplicative spectra of the
actual section algebras. Its group and arrow maps are

`(g • x)(b) = x(sectionAction(g).inv(b))`

and

`restrictionComap(f)(x)(b) = x(f.restriction(b))`.

The object and arrow evaluation lemmas give these formulas.
Each such map is continuous because it is pullback along a bounded map.
`invariantSpectrumActionFunctor_forget` identifies the entire underlying
topological diagram with the previously published
`Domain.toTopologicalSpace` diagram after full inclusion.

## Provenance and scope

This is internal construction from the actual domain category, the
constructed section actions, the spectrum functor and Mathlib's action
interfaces. It adapts the invariant-domain packaging and inverse-action
proof pattern of Worker 36's published
`StrictTestDomain/SpectralContinuousAction`. Here the domains are arbitrary
supplied full representations by positive-polyradius quotients.
The geometric action diagram is constructed first, then the existing
spectrum functor realizes it.

No nontrivial valuation, reducedness, nonzero quotient, nonempty spectrum
or nonempty domain is assumed. The target of the spectrum diagram is
`Action TopCat H`, so this unit asserts continuity for each fixed group
element and each restriction map. It supplies no proof of joint continuity
in the group and spectrum variables or continuity of section actions into
another domain spectral topology. Such conclusions require further
analysis and domain comparison. General analytic spaces, arbitrary compact
domains, étale sites and cohomology also remain outside this focused unit.
