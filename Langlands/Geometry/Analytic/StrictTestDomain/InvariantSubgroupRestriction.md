# Common open stabilizers and subgroup restriction of rational spectra

Author: Worker 36.

This derived construction starts with the Library's actual presented strict
affinoid algebra `P` over a complete ultrametric normed field `K`, a topological
group `G`, and `ρ : RationalSpectralAction G P`. It constructs common open
stabilizers for finite families of actual rational loci, changes the acting open
subgroup in the existing invariant rational domain category, and lifts finite
rational diagrams to diagrams of continuous equivariant spectra over the base.
The field, group, diagram-object and diagram-morphism universes are independent.

For a finite family `D : I → RationalData K P`, the definition
`finiteLocusOpenSubgroup ρ D` is Mathlib's `OpenSubgroup.iInfOfFinite` applied to
the already constructed open setwise stabilizers `ρ.locusOpenSubgroup (D i)`.
Its underlying subgroup is their actual intersection, with openness supplied
by finiteness. The theorem `mem_finiteLocusOpenSubgroup` identifies membership
with preserving every locus. The theorem `le_finiteLocusOpenSubgroup_iff`
identifies containment with containment in each individual stabilizer, so this
is the largest open subgroup preserving all the loci. An empty family gives
the whole group. No group element is required to fix the rational presentation
or individual spectrum points.

Given a prescribed open subgroup `U`, the definition
`finiteFamilyOpenSubgroup ρ U D` intersects this common stabilizer with `U`.
The module proves its exact membership and containment criteria, containment
in `U` and in each locus stabilizer, and equality with `U` for an empty family.
Thus the subgroup is constructed from the input family, rather than assumed.
The index type may lie in any universe; only its finiteness is used.

For open subgroups `V ≤ U`, the definition `openSubgroupInclusion` is the
continuous homomorphism `V → U` given by the identity on elements of `G`.
Continuity uses the two subtype topologies. A rational domain invariant under
`U` is invariant under `V` by transitivity of subgroup containment.
The definition `invariantRestrictionFunctor ρ h` uses Mathlib's
`ObjectProperty.ιOfLE` to obtain

```text
InvariantRationalDomain ρ U → InvariantRationalDomain ρ V.
```

It keeps every actual rational datum and every inclusion homomorphism.
In particular the associated quotient algebra and bounded algebra restriction
are unchanged. The construction `invariantRestrictionFullyFaithful` reuses
Mathlib's fully faithful inclusion of full subcategories. The module proves
exact equalities for forgetting invariance, the identity subgroup change, and
composition of subgroup changes.

The theorem `invariantSpectrumFunctor_restrict` proves an equality of functors:
changing invariant domains from `U` to `V` and then taking their continuous
spectra agrees with first taking the `U`-spectrum diagram and then applying
`ContAction.res` along the continuous inclusion `V → U`. Both objects and
maps agree by their definitions: the spectrum is still the actual
`BanachSpectrum d.algebra`, an element acts by inverse pullback of the same
bounded section automorphism, and an inclusion acts by comap of the same
bounded restriction. No replacement by merely isomorphic topological spaces
is needed. The theorems `restrictedGlobalSpectrum_restrict` and
`invariantSpectrumToBase_restrict` give the corresponding exact compatibility
for the global spectrum and its actual equivariant structural maps.

Suppose `F : J ⥤ RationalData K P` and the type of objects of `J` is finite.
The definition `finiteInvariantDiagram ρ U F` lifts `F` to the full subcategory
of rational domains invariant under
`W = finiteFamilyOpenSubgroup ρ U F.obj`. Mathlib's `ObjectProperty.lift`
uses the proved inclusion of `W` in each object stabilizer. There is no
additional equivariance hypothesis on the input arrows: the published
restriction-equivariance theorem already applies to every inclusion between
invariant rational loci. Forgetting invariance recovers `F` exactly.
Only the objects of `J` must be finite; no finiteness of its hom types is used.

Composing this lift with the published `invariantSpectrumOverFunctor` defines
`finiteInvariantSpectrumOverDiagram ρ U F`. Its value is a diagram in
`Over (ρ.restrictedGlobalSpectrum W)` in the category of continuous `W`-actions.
The objects are the actual quotient spectra, the arrows are the continuous
equivariant comaps of the input bounded restrictions, and the structural maps
are the actual quotient-to-base spectrum maps. Forgetting the structural maps
and actions gives exactly `F ⋙ RationalData.toTopologicalSpace K P`.

The geometric motivation is Berkovich's unfinished *Etale equivariant sheaves
on p-adic analytic spaces* (1995–1996), section 1.1, printed/PDF pp. 1–3.
The automorphism topology uses finite families of compact analytic domains
and function tests; its displayed basic subgroups preserve those domains.
The same section defines continuous group actions, equivariant morphisms,
and morphisms of spaces with operators involving a continuous homomorphism
of acting groups. The finite intersection and subgroup-change constructions
here are internal consequences of the Library's restricted rational spectral
action and Mathlib's open subgroup and continuous action constructions.
They are not a verbatim theorem of the manuscript. Section 1.2 on p. 3
motivates later equivariant site constructions; no morphism of those full
sites or topoi is constructed here.

The rational algebras and bounded maps are inherited from the published
`SpectralOverBase` and `SpectralContinuousAction` interfaces. Their actual
quotient presentations implement the restricted unit-radius rational
construction of Berkovich's *Non-archimedean analytic spaces*, Trieste lectures
(2009), Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p. 9.
This module requires no unpublished covering topology. It constructs no
arbitrary-radius domains, scalar descent, structure sheaf, analytic atlas,
or full etale or quasi-etale site, and asserts no identification with the full
analytic automorphism topology. Trivial valuations, zero or nonreduced
quotients, empty loci, empty spectra, and empty finite diagrams are retained.

The registered Equish source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its PDF member has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The Trieste source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
