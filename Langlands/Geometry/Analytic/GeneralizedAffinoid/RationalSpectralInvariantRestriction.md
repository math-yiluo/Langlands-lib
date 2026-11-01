# Subgroup restriction of represented-domain spectral rational diagrams

Author: Worker 56.

This internal construction compares the actual positive-radius rational
section, spectrum and locus diagrams when an open subgroup `J` is replaced
by an open subgroup `H ≤ J`. Its entry point is
`spectralInvariantSpectrumLocusRestrictionIso`.
Let `K : Type u` be a complete ultrametric normed field, let
`A : PresentedAffinoidAlgebra K` be an actual presented affinoid quotient,
and let `G : Type v` be a topological group. Fix
`rho : DomainSpectralAction G A`. All declarations retain completeness,
and the field and group universes are independent.

## Full chart inclusion

`spectralInvariantChartRestriction` is the full-subcategory inclusion from
`SpectralInvariantChart rho J` to `SpectralInvariantChart rho H`.
Its invariance witness composes `H ≤ J` with the existing inclusion of `J`
in the full stabilizer of the chart's actual represented locus.
Every quotient presentation and every original bounded restriction is
unchanged. `spectralInvariantChartRestrictionFullyFaithful` supplies full
faithfulness from Mathlib's full-subcategory inclusion, and the corresponding
full and faithful instances are included.

The object and arrow formulas state equality with the original chart and
bounded arrow. Forgetting invariance recovers the original full inclusion
into `RationalChart K A`. Identity and composition of subgroup restrictions
hold exactly. `spectralInvariantDomainFunctor_subgroup` identifies the two
routes through the existing represented-domain inclusion and
`rho.invariantDomainRestriction`.

The continuous homomorphism `openSubgroupInclusion` is imported from
`StrictTestDomain.RationalAutomorphism.RationalSpectralAction` via
`DomainInvariantSubgroupRestriction`. It sends an element of `H` to the same
ambient element regarded as an element of `J`, with the inherited subgroup
topologies. Its source namespace imposes no strict-radius hypothesis here.
`spectralInvariantStabilizerInclusion_subgroup` identifies direct inclusion
in the full local stabilizer with inclusion through `J`.

## Section, spectrum and locus coherence

`spectralInvariantSectionAction_subgroup` equates the entire constructed
spectral section action on an `H`-invariant chart with restriction of its
`J`-action along this continuous inclusion. The restriction functor is
`DomainSpectralActionCategory.restrict`, retaining the actual quotient
algebra and all bounded operators. The equality of `actionAut`
homomorphisms in
`spectralInvariantSectionAction_actionAut_subgroup` retains the bounded
inverses as well. These identities concern the full constructed algebra
actions; they do not recover algebra maps from their spectrum operators.

`spectralInvariantBoundedPresheaf_subgroup` identifies the whole section
presheaves after changing chart indices and restricting the acting group.
Every original bounded restriction arrow is retained.
`spectralInvariantBaseAction_subgroup` identifies the restricted ambient
algebra action, and `spectralInvariantBaseMapNat_app_subgroup` states that
each equivariant structural bounded base map is precisely its original
component restricted to `H`.

`spectralInvariantLocusFunctor_subgroup` equates the two entire continuous
locus diagrams, including every actual subspace inclusion.
`spectralInvariantSpectrumFunctor_subgroup` gives the analogous equality
for the continuous quotient-spectrum diagrams. The latter retain inverse
pullback for each group operator and ordinary bounded pullback for each
restriction arrow. `spectralInvariantGlobalSpectrum_subgroup` identifies
the two ambient continuous spectrum actions, and
`spectralInvariantSpectrumToBase_subgroup` retains the original structural
spectrum map over that ambient action.

`spectralInvariantSpectrumLocusRestrictionIso` restricts the existing
natural continuous equivariant spectrum-locus homeomorphism for `J` along
`H → J`. Its type uses the `J`-invariant chart category reinterpreted as
`H`-invariant. `spectralInvariantSpectrumLocusRestrictionIso_eq` identifies
this construction with restriction of chart indices in the `H`-diagram.
The forward and inverse point formulas are the original
`d.obj.locusHomeomorph` and its inverse. Forgetting the continuous actions
recovers exactly the original rational `spectrumLocusIso` restricted to
the full `J`-invariant chart category.

All displayed coherence proofs are definitional equalities, using proof
irrelevance for invariance, continuity and equivariance witnesses. The new
constructions are the full chart inclusion, its full-faithfulness witness
and the restricted natural isomorphism. The imported modules have already
constructed the actual bounded maps, continuous actions and natural
homeomorphisms; none is an extra output-object assumption here.

## Provenance and sources

Worker 56 adapts the published `RationalNormInvariantRestriction` and
`DomainInvariantSubgroupRestriction` constructions to the continuous
spectral rational diagrams of `RationalSpectralInvariantActions`.
The norm-continuous predecessor uses quotient-norm orbit continuity;
this module instead uses the existing represented-domain spectral
automorphism topology and its continuous action category throughout.
No implication between these continuity hypotheses is asserted.
This is an internal categorical coherence construction, rather than a
numbered result attributed to the following original sources.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
printed/PDF p.9 Definition 2.2.1, Exercise 2.2.2(ii)-(iii), and p.10
Fact 2.2.3(i) and Definition 2.2.7, supplies the inherited conventions for
represented affinoid domains, positive-radius rational quotients,
spectrum/locus identification and domain embeddings. The imported charts
carry explicit unit-ideal generation, a sufficient no-common-zero condition;
its converse is not claimed here. Registered source ID:
`berkovich-2009-trieste-analytic-spaces`; PDF SHA256:
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1996 manuscript, section 1.1, printed/PDF pp.1-3, motivates continuous group
actions, equivariant morphisms and continuous changes of acting group.
Its full analytic automorphism topology tests compact analytic domains and
spectral displacement of functions. The represented-domain topology used
here is not identified with all of those compact-domain tests.
Registered collection ID:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
collection content SHA256:
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256:
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

Arbitrary positive real polyradii, trivial valuations, nilpotents, zero
quotients and empty spectra or loci remain allowed. The input imposes no
quotient-norm orbit-continuity or spectral-faithfulness assumption.
Finite-site functoriality and sheaf descent, general analytic atlases,
continuous restriction to arbitrary represented domains, full analytic
automorphism-topology comparison, analytic etale/quasi-etale sites,
compact/distinguished lifting and the Harris tower remain separate
construction obligations.
