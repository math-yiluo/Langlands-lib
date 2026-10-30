# Finite-cover refinement categories under bounded base equivalences

Worker 56 constructs an equivalence between the actual finite full-domain
cover refinement categories before and after a bounded equivalence of their
ambient presented affinoid algebras. Both functors retain the chosen component
indices and the actual bounded algebra restrictions.

## Inputs and provenance

The coefficient field `K : Type u` is complete and ultrametric. Each
`PresentedAffinoidAlgebra K` is a finite positive-polyradius Tate algebra
modulo a closed ideal, with its actual quotient norm. A `Domain K A`
retains its representing quotient algebra, bounded structural map, closed
spectrum locus, exact spectrum image and universal factorization against
all presented affinoid tests.

The imported `DomainCoverBaseTransport` constructs a finite cover
`c.transportBase e` of `Domain.transportBase e V` from a cover `c` of `V`
and an actual bounded algebra equivalence `e : BoundedAlgEquiv K A B`.
It retains the quotient algebras and restrictions and transports loci by
the preimage under the continuous spectrum homeomorphism. The imported
`DomainCoverRefinement` supplies a category whose morphisms choose, for
each finer component, a coarser component and an actual full-domain arrow.
Distinct chosen index functions remain distinct morphisms.

The underlying domain notion is Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), registered source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
Definition 2.2.1, printed/PDF p.9. Definition 2.2.7 on p.10 gives the
affinoid-domain embedding context. The finite-cover category equivalence
here is an internal consequence of the published domain and cover
transport constructions. It is not a separately named theorem from the
source, nor a use of the algebra-section descent results on p.10.

## Forward transport and spectrum maps

`Refinement.transportBase` retains `r.index` and applies the published
`Domain.transportBaseMap` to every component arrow. That domain
construction keeps the actual bounded restriction. The index and
restriction equations are definitional. Refinement identity and
composition are preserved: `Refinement.ext` reduces their equality to
equality of the index functions, using the published uniqueness of actual
full-domain arrows.

`transportBaseFunctor` bundles these object and morphism constructions.
`Refinement.transportBase_spectrumMap` proves that its continuous map on
the disjoint unions of component quotient spectra is unchanged. Both
unions have definitionally the same quotient algebras, and the component
maps are the same actual seminorm pullbacks.
`transportBase_spectrumMap_over_target` combines the transported
refinement triangle with the published cover transport triangle. Thus
the unchanged finer spectrum map lies over the original target locus
after applying its concrete spectrum-induced locus homeomorphism.

The singleton identity cover is already preserved by the imported object
transport. `transportBase_toSingleton` additionally identifies the
transported canonical terminal arrow with the canonical terminal arrow
of the transported cover, retaining the selected singleton index.

## Inverse and categorical equivalence

For an arbitrary cover of the transported target,
`transportBaseInverseObj` transports every component and restriction
back with `e.symm`. The resulting target is initially the round-trip
transport of `V`; composing each target arrow with
`Domain.transportBaseRoundTripIso e V` restores the exact original
target. Coverage follows from inverse cover transport and the published
round-trip equality of the actual target loci. This constructs the
inverse object from the supplied cover, without assuming that it was
previously obtained by forward transport.

`transportBaseInverse` transports refinement arrows back with `e.symm`,
again preserving indices and bounded restrictions. Its identity and
composition laws use refinement extensionality.
`transportBaseUnitIso` and `transportBaseCounitIso` use the identity
index function in both directions. Each component arrow is the
corresponding published actual domain round-trip isomorphism, whose
bounded algebra restriction is the identity on the retained quotient
algebra. The inverse laws, naturality and triangle identity reduce by
refinement extensionality to the retained index functions.
The entry `transportBaseEquivalence` bundles these concrete functors and
natural isomorphisms as a Lean categorical equivalence.

All constructions allow empty covers and loci, zero quotient algebras,
arbitrary finite positive polyradii and trivial valuations. They require
an actual bounded algebra equivalence of the ambient bases. Pullbacks
along arbitrary analytic morphisms, rational-domain existence,
algebra-section gluing, analytic atlases and etale sites remain separate
obligations.
