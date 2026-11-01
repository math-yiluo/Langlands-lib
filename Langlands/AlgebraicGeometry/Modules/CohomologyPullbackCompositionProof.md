# Composition of canonical pullback on actual relative cohomology

The theorem `relativeCohomologyPullbackCompositionStatement` proves the published
`RelativeCohomologyPullbackCompositionStatement.{u}`. For every commutative base
ring, three actual schemes over its spectrum, composable morphisms
`h : Y ⟶ X` and `k : Z ⟶ Y`, actual structure-sheaf module `M` on `X`, and
`n : ℕ`, pullback along `h` followed by pullback along `k`, and then the forward
coefficient identification `Scheme.Modules.pullbackComp k.left h.left`, equals
pullback along `k ≫ h`. The proof includes degree zero and has no additional
hypotheses. It proves the composition component; the complete five-law
conjunction is a separate result.

## Provenance

This is an internal coherence proof for the constructions in
`CohomologyPullback`, `CohomologyPullbackSections`, and `DerivedPlus`. It uses
Mathlib's adjunction mates, injective derivability, localization, and single
complex comparison maps. The general construction by an adjunction/coefficient
map into a pushed-forward injective resolution, followed by an inverse acyclic
comparison, is explained in the Stacks Project, *Cohomology of Sheaves*,
“Functoriality of cohomology”, tags 01F7–01FB. The project source is
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, `cohomology.tex:2327–2432`.
That passage supplies the general framework; the exact scheme-module
coefficient transports and the coherence equations proved here are internal
derivations from the published definitions.

## The comparison on complexes

The generic lemma `DerivedPlus.exists_acyclicComparison` starts with a natural
map from termwise application of a functor into a second complex functor,
invertible on bounded below complexes of injective objects. Injective
resolution derivability makes the second functor derivable as well. Comparing
its total right derived functor with the first one gives an isomorphism: this
is checked on localized injective complexes, which are essentially surjective.
Its inverse constructs the required natural comparison and proves its
factorization equation. The lemma
`DerivedPlus.natTrans_ext_on_injective_complexes` proves that transformations
into a localized functor agree if they agree on injective complexes, using an
injective resolution of each complex and cancellation of its localized
quasi-isomorphism.

For a scheme morphism `h`, the termwise sections comparison and the derived
unit give the input for this construction. The necessary invertibility is
proved by `isIso_unit_pushforward_injective_complex`: pushforward of each
injective term is acyclic for relative global sections, so the published
acyclic-terms derived-unit theorem applies. This is a fact about resolution
terms, with no acyclicity assumption on the coefficient module.
`pushforwardDerivedSectionsComparison` is the resulting transformation β,
normalized by `pushforwardDerivedSectionsComparison_fac`.

`pullbackComposition_sections` checks the sections comparison for a composite
on every open set. The equation reduces to functoriality of the module
presheaf. Its termwise version is
`pullbackComposition_sectionsComplex`. To prove
`pushforwardDerivedSectionsComparison_comp`, the proof uses the generic
extensionality lemma and evaluates on an injective complex. The unit on its
twice-pushed-forward complex is invertible, by transport along pushforward
composition from the corresponding acyclic unit. Precomposing with that unit,
β's factorization equation, unit naturality, and sections coherence prove
composition of β.

## Removing the chosen resolutions

`DerivedPlus.singlePlusFunctor`, `singlePlusQIso`, and `singlePlusMapIso`
relate degree-zero objects, their bounded below complexes, and localization.
The generic equation `singlePlusMapIso_comp` proves their compatibility with
composition of functors. After faithful inclusion into raw complexes,
extensionality from a single complex reduces it to naturality of the given
functor-composition isomorphism in degree zero.

`pullbackResolutionAugmentation_eq_single` expresses the actual raw
augmentation as the single-complex map of the adjunction unit followed by the
single/pushforward comparison and the resolution augmentation. Its proof
checks degree zero and the extension comparison. Localization, naturality of
the single/localization isomorphisms, and faithful inclusion give
`pullbackDerivedAugmentation_eq_single`. The formula
`singleIsoOfResolution_hom_eq` identifies the chosen-resolution isomorphism
with the localized augmentation. Substitution into the published pullback,
β's factorization, and naturality along that augmentation give
`relativeDerivedSectionsPullback_eq_single`.

The transformation `pushforwardSingleDerivedSectionsComparison`, denoted τ,
combines the single/localization comparisons with β. In particular,
`relativeDerivedSectionsPullback_eq_unit_comparison` identifies the actual
pullback with the derived-complex map of the adjunction unit followed by τ.
The equation `pushforwardSingleDerivedSectionsComparison_comp` follows from
β naturality and composition, `singlePlusMapIso_comp`, and naturality of the
single/localization comparison; the middle inverse/forward comparisons
cancel.

## Composition and homology

`pullbackComposition_unit` is the equation for the units of the actual
pullback/pushforward adjunctions. It follows from `unit_conjugateEquiv`,
Mathlib's `conjugateEquiv_pullbackComp_inv`, and the unit formula for a
composite adjunction. Naturality of τ moves the second unit through the first
comparison. Composition of τ and this unit equation yield
`relativeDerivedSectionsPullback_comp_inv`, with the inverse coefficient
identification on its right. Composing with the forward identification and
cancelling the coefficient isomorphism proves
`relativeDerivedSectionsPullback_comp`.

Finally, the definition of `relativeCohomologyPullback` expresses it through
homology of the actual derived map and the chosen-resolution homology
isomorphisms. The middle homology isomorphisms cancel. Naturality
`DerivedPlus.homologyIso_hom_naturality` moves the coefficient map through the
last comparison, and functoriality of homology applies the derived composition
equation. This proves `relativeCohomologyPullback_comp` and hence the exact
published proposition.
