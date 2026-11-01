# Full-domain localization along a specified embedded domain

Author: Worker 36.

This module constructs
`Domain.localizationEquivalenceOfInjective U hU :
Domain K U.algebra ≌ Over U`.
Here `U : Domain K A` is an existing full represented affinoid domain and
`hU : Function.Injective U.spectrumMap` is a proof for its particular
structural spectrum map. All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain`.

The coefficient field is any complete ultrametric normed field. The actual
algebras are the existing finite positive-polyradius closed Tate quotient
presentations. The representation property tests every such affinoid algebra.
There is no strictness, nontrivial-valuation, reducedness, nonzero-algebra,
nonempty-spectrum or injectivity assumption on arbitrary inner domains.

## Extension and actual bounded maps

`extendOfInjective U hU V` retains exactly `V.algebra`, composes the two
actual bounded structural maps, and uses `U.spectrumMap '' V.locus` as its
ambient locus. Its representation proof is the imported
`Represents.comp_of_injective`. That proof first factors a bounded test map
through `U`; injectivity of the specified outer spectrum map then puts the
factor's image in `V.locus`, so the full property of `V` factors it again.
The two uniqueness clauses prove uniqueness for the composite. Compactness
and Hausdorffness make the image locus closed.

The projection lemmas give the unchanged algebra, composed structural map,
and image locus as definitional equalities.
`extendOfInjective_locus_subset` gives containment in `U.locus`.
`extendOfInjective_spectrumMap` identifies the structural spectrum map with
the composite, by extensionality of the actual seminorms.
`extendOfInjectiveInclusion` stores exactly `V.baseMap` as the restriction
of the ambient inclusion into `U`.

`extendOfInjectiveFunctor` retains the actual bounded restrictions between
inner domains. Associativity and their base equations give the equations
over `A`. `fullyFaithfulExtendOfInjective` recovers each equation over
`U.algebra` by `U.represents.hom_ext`, which cancels precomposition with
`U.baseMap` using full test-map uniqueness. This constructs inverse maps on
hom sets and the associated `Full` and `Faithful` instances.
The two `extendOfInjectiveFunctor_comp_to...` lemmas give literal equality
of the actual affinoid and topological realizations with those before
extension.

`extendOfInjectiveOverFunctor` also stores the actual inclusion into `U`.
Its triangle equation is the original bounded base equation. Its projection
to the ambient domain category is exactly `extendOfInjectiveFunctor`.
Both functors have explicit restriction projection lemmas.

## Relative inverse and equivalence

The inverse is the imported `U.relativeFunctor`. That construction requires
no injectivity: it assigns to an ambient inclusion `f : V ⟶ U` the same
`V.algebra`, structural map `f.restriction`, and actual spectral range
`Set.range f.spectrumMap`. The imported relative representation proof uses
the two full representation properties and cancellation. The image of that
locus under `U.spectrumMap` is exactly `V.locus`. Under the particular
`hU`, the imported `relative_locus_eq_preimage_of_injective` also identifies
it with `U.spectrumMap ⁻¹' V.locus`.

`relativeExtendOfInjectiveIso` and `extendRelativeOfInjectiveIso` construct
the two round-trip comparisons. Both maps in both comparisons are bounded
identities on the unchanged represented algebra. For the inner round trip
the base maps are definitionally equal. For the ambient round trip its base
equations are `f.comp_baseMap` and its reverse. Arrow extensionality proves
the inverse identities. Four projection lemmas expose these bounded
identity maps, and two locus lemmas recover the original represented subsets.

`localizationEquivalenceOfInjective` assembles those comparisons as natural
unit and counit isomorphisms in the full domain and over categories.
Naturality and the triangle identity are equalities of actual arrows,
proved by their restriction extensionality. The over category keeps the
whole commuting inclusion triangle.

`extendOfInjectiveLocusHomeomorph` restricts the specified continuous
injective spectrum map to a homeomorphism of `V.locus` with its extended
locus. Compactness and Hausdorffness give the required embedding, and its
coefficient projection is exactly `U.spectrumMap`.
`extendOfInjective_spectrumMap_injective` proves that an inner domain whose
own spectrum map is injective remains so after extension, by the composite
spectrum equation and the two specified injectivity proofs.

## Provenance and remaining scope

The original source is V. G. Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p. 8, gives the category dual to actual bounded
affinoid algebra homomorphisms. Definition 2.2.1, printed/PDF p. 9, gives
the closed-image and unique-factorization property used throughout.

The equivalence and retained-algebra identities are internal derived
packaging of that representation property, the proved conditional
composition lemma, and the relative representation construction. This
generalizes the existing rational-chart and original-atlas-containment
localization constructions to any particular full domain for which `hU`
is available. It does not invoke Fact 2.2.3(i), printed/PDF p. 10, to supply
that proof. General injectivity of full-domain spectrum maps remains a
separate proof obligation. No pending proposition is assumed as an axiom
or used as an output-object input. Unrestricted domain composition, full
atlas saturation, structure sheaves, analytic sites and Harris towers
remain outside this module's conclusions.
