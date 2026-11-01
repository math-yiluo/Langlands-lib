# Subgroup restriction of represented-locus actions and equivariant maps

Author: Worker 56.

Fix a complete ultrametric normed field `K : Type u`, a presented finite
positive-polyradius affinoid quotient `P`, a topological group `G : Type v`
and a supplied `ρ : DomainSpectralAction G P`. For open subgroups `J ≤ H`,
the published `invariantDomainRestriction` keeps each actual represented
domain and its bounded restrictions, and regards it as `J`-invariant.
The published `openSubgroupInclusion` is the continuous homomorphism
`J → H` sending each element to the same element of `G`.

`invariantLocusOperator_subgroup` identifies the operator on this
restricted domain with the original operator evaluated at the included
group element. Both apply the same ambient inverse-pullback operator
and retain its point in the same represented locus.
`invariantLocusActionFunctor_subgroup` gives the corresponding equality
of whole diagrams with restriction by Mathlib's `Action.res`.
`invariantSpectrumToLocus_subgroup` identifies the structural
spectrum-to-locus quotient after restriction with the original
equivariant quotient restricted by that same functor. All three
equalities are definitional, including their actual continuous maps.

`equivariantLocusMapRestriction` sends an equivariant continuous map
out of an `H`-invariant represented locus to the same continuous map,
with source and target actions restricted to `J`. The topological target
lies in its own independent universe `w`. The equivariance equation at
`g : J` is the original equation at its image in `H`; no point or
replacement map is chosen.

The value lemma exposes the unchanged continuous map. The reflexive
and composition laws identify identity restriction and successive
restriction with their direct counterparts. The postcomposition law
shows compatibility with ordinary equivariant morphisms of targets.
These are equalities of the actual map subtypes, with proof
irrelevance identifying their equivariance witnesses.
When the target has universe `u`, the final theorem
`equivariantLocusMapHomEquiv_subgroup` identifies this construction
with restriction of the ordinary morphism in `Action TopCat H`.

This is internal derived content from `DomainInvariantLocus`,
`DomainInvariantSubgroupRestriction`, `DomainEquivariantGluing` and
Mathlib's action restriction. No new literature assertion is made.
Representations, bounded restrictions, structural maps and all locus
topologies remain those of the imported actual domains. Empty loci,
zero quotients, nilpotents and trivial scalar valuations are allowed.
The actions supply continuous fixed-element operators; joint
continuity remains separate. Analytic structure sheaves, analytic
etale sites and the Harris specialization remain further work.

The subgroup inclusion used here is the published
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.openSubgroupInclusion`,
reused through `DomainInvariantSubgroupRestriction`.
