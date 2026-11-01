# Continuous equivariant locally constant descent for finite weighted rational covers

Author: Worker 56. Internal construction, reusing Worker 36's invariant-action
pattern through the rational norm-action helpers.

`RationalChart.FiniteCover d` consists of a natural number `size`, actual
weighted rational charts indexed by `Fin size`, their original bounded
restriction arrows to `d`, and point coverage of `d.locus`. The finite index
may be empty. `toDomainCover` retains the exact quotient algebras, structural
maps and bounded restrictions in the represented-domain cover. Its component
map is the original component spectrum-to-locus homeomorphism followed by
inclusion into the target locus. Equivalently it is the original bounded
spectrum restriction followed by the target's spectrum-locus homeomorphism.
The component-map and restriction identities in Lean prove these descriptions.

`DiscreteCompatibleFamily C` is the entire subtype of locally constant
functions on the component spectra satisfying
`componentMap i x = componentMap j y` implies `f i x = f j y`, for every pair
of components and points. This includes equal-image equations within a single
component. It is definitionally the existing represented-domain compatible
family, with the rational spectrum types displayed explicitly for elaboration.
Each component function space has its discrete topology; the family space
retains the inherited finite product and subtype topology.

The action input is a topological group `G`, bounded base-algebra automorphisms
`rho`, and norm-continuity of every forward orbit `g ↦ (rho g).hom a`. For any
prescribed open subgroup `U`, `normOpenSubgroup` intersects `U` with the full
setwise stabilizer of the target locus and all component loci. Existing
openness and finite-intersection results construct this as an open subgroup
with its inherited topology. The membership equivalence and containment
criterion prove that it is the largest open subgroup inside `U` preserving
the target and every component. The invariant target, components and arrows
retain the original charts and bounded restrictions.

`normComponentToLocus` composes the established equivariant rational
spectrum-locus homeomorphism with the established locus restriction. Its
underlying map is the original component map. Its equivariance proves that
componentwise inverse precomposition preserves every compatible-family
fiber equation. `normCompatibleSmul_apply` displays this action using the
original bounded seminorm pullback for the inverse group element. The action
laws follow componentwise from the existing locally constant function action.
The compact-action theorem supplies joint continuity on each discrete
component function space. Finite product and subtype continuity then give
the jointly continuous action `normCompatibleAction` on all compatible
families, with the original group and family topologies.

`normLocallyConstantDescentIso` uses the existing represented-domain
restriction and gluing maps. That gluing descends through the quotient from
the finite disjoint union of the actual component spectra, using the complete
fiber equations. Its inverse identities are the existing quotient-descent
identities; equivariance follows from the component-map commutation equation.
Both function spaces are discrete, so the two maps are continuous. This gives
an isomorphism of continuous actions from all locally constant functions on
the target locus to the full compatible-family space. The forward evaluation
is `f (componentMap i x)`, and the inverse recovers `f i x` at that same point.

`normSpectrumLocallyConstantDescentIso` composes this with the inverse of the
established continuous-action-valued locally constant presheaf comparison.
Thus it uses the original target spectrum-locus homeomorphism in both
directions. The forward map on component `i` evaluates as
`f ((c.map i).spectrumMap x)`, with the original bounded restriction unchanged.
The inverse evaluation theorem recovers each input component function at
that spectrum image. These are isomorphisms on the entire indicated function
sets, rather than assumptions of descent or equivariance.

The field is complete and ultrametric. Field, group and coefficient universes
are independent. Arbitrary positive real radii, trivial valuations, nilpotents,
zero quotient algebras, empty spectra and loci, empty covers of empty targets,
and arbitrary empty or nonempty coefficient sets are retained. Coefficients
require no topology or action. Rational charts retain explicit unit-generation
data; no converse from absence of common zeros is asserted.

This is an internal derivation from Worker 56's `DomainLocallyConstantCoverAction`
and `RationalNormLocallyConstantPresheaf`, together with the common-stabilizer
construction in `RationalNormInvariantOverBase`. The rational norm-action
helpers reuse Worker 36's invariant-action pattern. No `DomainSpectralAction`
is required. The finite-cover locally constant descent and its common subgroup
are internal constructions rather than results attributed to the originals.

The underlying geometric conventions are Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`:
printed/PDF p.4 Example 1.2.2(v) and Definitions 1.2.3/1.2.5 for positive-radius
Tate algebras and bounded seminorm spectra; pp.7-8 Definitions 2.1.2/2.1.11
for quotient presentations and bounded morphisms; pp.9-10 Definition 2.2.1,
Exercise 2.2.2(ii), Fact 2.2.3(i) and Definition 2.2.7 for represented domains,
weighted rational inequalities, their spectrum identification and embeddings.
The group-action motivation is the unfinished 1995-1996 manuscript
*Etale equivariant sheaves on p-adic analytic spaces*, section 1.1 printed/PDF
pp.1-2, literature
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member PDF SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

This unit does not identify norm-orbit continuity with the full analytic
automorphism topology, construct general analytic atlases, prove that the
analytic algebra presheaf is a sheaf, construct analytic etale/quasi-etale
sites, or construct the Harris tower.
