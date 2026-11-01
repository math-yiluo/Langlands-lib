# Subgroup restriction of continuous weighted rational diagrams

Author: Worker 56.

This internal construction compares the actual weighted rational diagrams
under passage from an open subgroup `J` to an open subgroup `H ≤ J`.
Its entry point is `normInvariantSpectrumLocusRestrictionIso`. The setting
and the actual chart, section, spectrum and locus constructions are those of
`RationalNormInvariantActions`: an ultrametric normed field `K`, a presented
positive-polyradius affinoid algebra `A`, a topological group `G`, a bounded
automorphism homomorphism `ρ`, and continuity in the quotient norm of each
forward base-algebra orbit. Field and group universes are independent.

`normInvariantChartRestriction` is the full-subcategory inclusion from the
`J`-invariant charts to the `H`-invariant charts. Its invariance witness
composes `H ≤ J` with the existing inclusion of `J` in the full local locus
stabilizer. Every chart presentation and every original bounded restriction
map is retained. `normInvariantChartRestrictionFullyFaithful` constructs its
full faithfulness using Mathlib's full-subcategory inclusion. Forgetting
invariance gives the original inclusion into the actual rational chart
category; identity and composition of subgroup restrictions hold exactly.

The module reuses the published continuous homomorphism
`StrictTestDomain.RationalAutomorphism.RationalSpectralAction.openSubgroupInclusion`.
It sends each element of `H` to the same ambient element regarded as an element
of `J`, with the inherited subgroup topologies. Its name does not impose a
strict radius or a strict affinoid hypothesis on this construction.
`normInvariantStabilizerInclusion_subgroup` identifies direct and two-step
continuous inclusions into each chart's full local stabilizer.

Consequently the direct `H`-locus action equals restriction of the `J`-action
along that continuous inclusion. The corresponding equality of entire locus
functors retains every original continuous subspace inclusion. These
constructions do not require completeness of `K`.

With `K` complete, the same identities hold for the actual quotient-norm
continuous section actions. The equality of their `actionAut` homomorphisms
retains the complete bounded maps and inverses. The bounded section
presheaves agree after changing chart indices and restricting the group;
each equivariant structural base-map component is exactly the restriction
of its original component. No bounded map or equivariance witness is added
as an assumption. The complete jointly continuous spectrum functors likewise
agree under these operations. The actions still use inverse pullback of
actual multiplicative seminorms, and arrows still use the original bounded
restriction pullbacks.

`normInvariantSpectrumLocusRestrictionIso` restricts the published natural
continuous equivariant homeomorphism from spectra to loci along `H → J`.
Its type is the comparison on the original `J`-invariant charts reinterpreted
as `H`-invariant. `normInvariantSpectrumLocusRestrictionIso_eq` proves that
this is exactly the alternative construction by restriction of chart indices
in the `H`-diagram. The forward and inverse point formulas are the unchanged
`d.obj.locusHomeomorph` and its inverse. Forgetting the continuous actions
recovers exactly the original rational spectrum-locus natural homeomorphism
on the `J`-invariant chart category.

The Lean comparisons are definitional equalities, using proof irrelevance
for invariance, continuity and equivariance witnesses. The new constructions
are the full chart inclusion, its full-faithfulness witness and the
restricted natural isomorphism. They reuse the actual constructions and
proved obligations of the imported modules.

## Provenance and scope

The subgroup-change pattern follows Worker 56's published
`DomainInvariantSubgroupRestriction`; the current module applies it to the
norm-continuous rational diagrams. Its input is norm-continuity of the
base-algebra orbits, with no identification with the full analytic
automorphism topology.

This is an internal categorical coherence construction, not a new theorem
attributed to the literature. The underlying geometric conventions are those
recorded in `RationalNormInvariantActions`: Berkovich's *Non-archimedean
analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
printed/PDF p.4, Example 1.2.2(v), Definitions 1.2.3 and 1.2.5; pp.7–8,
Definitions 2.1.2 and 2.1.11; pp.9–10, Definition 2.2.1,
Exercise 2.2.2(ii), Definition 2.2.3 and Fact 2.2.7.
The continuous-group-action motivation is Berkovich's unfinished
1995–1996 manuscript *Étale equivariant sheaves on p-adic analytic spaces*,
registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`,
section 1.1, printed/PDF pp.1–2. Neither source is claimed to state this
Lean packaging or the incomplete-field locus-only extension.

Arbitrary positive real radii, trivial valuations, nilpotents, zero
quotients and empty loci or spectra remain allowed. General analytic
atlases, arbitrary compact or distinguished-domain preservation, sheaf
descent, analytic étale and quasi-étale sites, and the Harris tower remain
separate construction obligations.
