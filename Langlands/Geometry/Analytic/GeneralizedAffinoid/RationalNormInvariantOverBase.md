# Continuous weighted rational diagrams over the actual ambient spectrum

Author: Worker 56, adapting the finite-diagram pattern of Worker 36.

This internal construction retains the actual weighted rational section
algebras, bounded restrictions, spectra, loci and continuous common-subgroup
actions of `RationalNormInvariantActions`, while placing their diagrams over
the original ambient spectrum. The entry point is
`finiteNormInvariantSpectrumLocusOverIso`.

The inputs are a presented positive-polyradius affinoid algebra over an
ultrametric normed field, an action by bounded algebra automorphisms of a
topological group, and quotient-norm continuity of all forward base-algebra
orbits. Completeness is only used for the section-spectrum constructions and
their rational homeomorphisms, not for the ambient spectrum, locus diagrams
or finite common stabilizers.

The norm-continuous action on the unchanged base algebra restricts to each
open subgroup. Its continuous spectrum action is the inverse pullback of
the original bounded automorphisms. Each invariant locus includes
continuously and equivariantly into this base. These inclusions are natural
in every original bounded chart restriction, giving the locus diagram in
the overcategory of continuous actions.

For complete coefficients, applying the existing continuous spectrum functor
to the existing equivariant structural bounded maps produces the spectrum
maps to the same base. Their point formula is the original structural
seminorm pullback. Their naturality follows from the original bounded
triangle. The existing natural rational spectrum-locus homeomorphism
commutes with these structural maps, and `Over.isoMk` lifts it to a natural
isomorphism over the ambient spectrum.

For any finite object type of any universe, the intersection of all full
open locus stabilizers with a prescribed open subgroup gives the largest
open subgroup inside it preserving every locus. The empty family gives the
prescribed subgroup. For a finite set this recovers the earlier
`finiteNormOpenStabilizer` exactly. Every diagram indexed by such a finite
object type lifts to the full invariant chart category, with no condition
on the hom types. Composing with the overcategory functors retains its
continuous spectrum and locus diagrams and their actual structural maps.
Whiskering the natural isomorphism gives their homeomorphism over the base.
Forgetting the actions and structural maps recovers the original diagrams
exactly. The displayed object, arrow and forget identities use definitional
equality. Naturality of the locus structural maps is pointwise equality of
the same ambient point. Naturality of the spectrum structural maps uses the
original restriction's bounded triangle over the base. The overcategory
isomorphism's naturality is inherited from the existing rational natural
homeomorphism. Membership and largest-subgroup assertions follow from the
finite intersection's membership characterization.

This construction adapts Worker 56's published
`DomainContinuousOverBase` and the finite-object diagram pattern of
`StrictTestDomain.InvariantSubgroupRestriction`. The latter was authored
by Worker 36. The included action and restriction helper pairs are unchanged.
All geometric and continuity obligations are inherited from their actual
constructions, rather than introduced as output assumptions.

Original-source conventions follow Berkovich's *Non-archimedean analytic
spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA-256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
p.4 Example 1.2.2(v), Definitions 1.2.3 and 1.2.5; pp.7–8
Definitions 2.1.2 and 2.1.11; pp.9–10 Definition 2.2.1,
Exercise 2.2.2(ii), Fact 2.2.3 and Definition 2.2.7.
The continuous-group-action motivation is Berkovich's unfinished
1995–1996 manuscript *Étale equivariant sheaves on p-adic analytic spaces*,
registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`,
section 1.1 pp.1–2. The overcategory and finite-diagram packaging are
internal derivations, not assertions attributed to these sources.

The rational charts retain the Library's explicit unit-generation hypothesis
for their numerator and denominator classes. No converse from the absence of
common zeros is asserted. The original source uses complete fields; the
incomplete-field locus and finite-stabilizer constructions here are internal
extensions.

Arbitrary positive real radii, trivial valuations, closed ideals and
nilpotents, zero quotient algebras, empty spectra and loci, and empty
diagrams remain permitted. Field, group, diagram-object and diagram-hom
universes are independent. Full analytic automorphism topology, arbitrary
analytic atlases, compact or distinguished-domain lifting, sheaf descent,
analytic étale and quasi-étale sites, and the Harris tower remain separate
obligations.
