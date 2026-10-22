# Functoriality of pullback on ordinary étale cohomology

This module completes the identity and composition laws for the cohomology maps
constructed in `EtaleDerivedPullback`. Its parameters are actual schemes in
universe `u`, étale scheme morphisms, and a commutative coefficient ring
`R : Type u`, with module carriers also in universe `u`. All cohomology is the
published ordinary small-étale cohomology `EtaleDerivedSections.cohomology`.

For `f : Y ⟶ X`, `g : Z ⟶ Y`, and a module sheaf `F` on `X`, write `f^*` for
`restriction f (ModuleCat R)`. The published natural isomorphisms
`restrictionId` and `restrictionComp` identify identity restriction with the
identity functor, and `g^* f^*` with `(g ≫ f)^*`, respectively. The laws proved
here include those identifications explicitly; no strict equality of these
restriction functors is assumed.

## Computation using arbitrary resolutions

`restrictionDerivedIso_app_ofResolution` proves that the natural derived
comparison is computed by `restrictionDerivedIsoOfResolution f R I q` for
*any* injective resolution `I` of `F`. Apply the published comparison naturality
to the identity of `F` and a standard comparison lift from the selected
resolution to `I`; both derived maps of the identity disappear.

`cohomologyMap_app_ofResolution` consequently extends the earlier selected-
resolution formula to any `I`. It expands the right-derived section map and
cancels the forward and inverse resolution comparisons for the composite
functor. Thus pullback is computed by homology of the degreewise section map,
using `I` on `X` and `restrictedResolution f R I` on `Y`.

`cohomologyMapWithCoefficients_ofResolutions` also permits a coefficient-sheaf
morphism `α : f^*F ⟶ G` and any injective resolution `J` of `G`. Given a chain
map `φ : (restrictedResolution f R I).cocomplex ⟶ J.cocomplex` lifting `α`
in degree zero, the formula is

\[
H^q(X,F) \xrightarrow{\sim} H^q(\Gamma_X I)
\longrightarrow H^q(\Gamma_Y J)
\xrightarrow{\sim} H^q(Y,G).
\]

The middle map is the homology of the composite of
`resolutionSectionsMap f R I` and the application of sections to `φ`.
The lifting equation is explicit. Naturality of the inverse resolution
comparison for `Γ_Y` proves the formula. The previously constructed cohomology
map is independent of these auxiliary choices; the lemma does not redefine it
using a chosen lift.

## Section and resolution maps

`sectionsMap_id` and `sectionsMap_comp` transfer the corresponding published
terminal-object section laws through the natural isomorphism
`EtaleDerivedSections.sectionsIso`. The composition proof cancels the
intermediate section isomorphisms and uses naturality on `restrictionComp`;
the identity proof uses naturality on `restrictionId`.

`restrictionIdResolutionMap R I` applies the natural transformation
`restrictionId.hom` in every degree of `I`, giving a chain map from the
identity-restricted resolution to `I`. Its `_comm` lemma verifies that it lifts
the corresponding coefficient-sheaf identification; this is naturality at the
augmentation. `resolutionSectionsMap_id` then proves that the identity section
chain map followed by this identification is the identity chain map. The
proof checks each degree using `sectionsMap_id`.

`restrictionCompResolutionMap f R g I` similarly applies
`restrictionComp f (ModuleCat R) g` in every degree. It maps the twice-restricted
resolution to the resolution restricted along `g ≫ f`. Its `_comm` lemma
verifies compatibility with their augmentations. `resolutionSectionsMap_comp`
proves that the two successive section chain maps, followed by sections of
this resolution map, equal the direct section chain map. It checks each degree
using `sectionsMap_comp`.

## Cohomology laws

`cohomologyMap_id` states that pullback along `𝟙 X`, followed by the map on
cohomology of `restrictionId.hom.app F`, is the identity of `H^q(X,F)` for
every `q : ℕ`. Its proof uses the formula with coefficients, taking the same
resolution on both sides and `restrictionIdResolutionMap` as the lift. The
chain-map identity reduces the result to cancellation of the resolution
isomorphisms.

`cohomologyMap_comp` states that the composite

\[
H^q(X,F) \longrightarrow H^q(Y,f^*F)
\longrightarrow H^q(Z,g^*f^*F)
\longrightarrow H^q(Z,(f\circ g)^*F)
\]

is the direct pullback along the Lean composite `g ≫ f : Z ⟶ X`. In this
display the final coefficient identification is `restrictionComp.hom`; in
ordinary function notation the scheme map is `f ∘ g`.

The proof uses `I`, `restrictedResolution f R I`, and
`restrictedResolution (g ≫ f) R I` as its resolutions, with
`restrictionCompResolutionMap` for the last identification. After cancellation
of the intermediate resolution isomorphisms, functoriality of homology and
`resolutionSectionsMap_comp` give the result.

## Provenance and limits

This is internal construction and verification extending the published
`EtaleDerivedPullback` and `EtalePullback` interfaces. The new chain maps use
Mathlib's `NatTrans.mapHomologicalComplex`; the computation lemmas use
`InjectiveResolution.desc`, resolution naturality, and
`InjectiveResolution.rightDerived_app_eq` from
`CategoryTheory/Abelian/RightDerived.lean` at pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The proofs above describe the
implemented Lean route. No original-literature theorem is asserted.

The result addresses identity and composition for ordinary cohomology pullback
along étale morphisms. It does not yet identify these maps with the separate
scheme-automorphism action construction or construct a category of schemes
with coefficient sheaves. General scheme morphisms, scalar extension, analytic
sites, compact support, and Harris's specialized geometric objects remain
outside this unit.
