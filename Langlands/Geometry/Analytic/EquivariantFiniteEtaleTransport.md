# Structural-base transport of relative finite étale affinoid actions

Author: Worker 36.

This derived construction precomposes the structural map of an actual
finite étale affinoid object carrying a norm-continuous action. For an
equivariant bounded map `f : X ⟶ Y` whose underlying algebra map is
algebraically finite étale, an object `Y → B` becomes `X → Y → B`.
The target presented quotient algebra, its action, and every compatible
bounded equivariant arrow remain the same.

## Precomposition and its compatibility

Let `K` be an ultrametric normed field and `G` a group with a topology.
They have independent universes. The algebra categories do not require
continuity of the group operations or completeness of `K`.

`AlgebraicallyFiniteEtaleAffinoidActionUnder.reindex f hf` includes the
published full subcategory under `Y`, applies Mathlib's actual
`Under.map f`, and lifts to the full finite étale subcategory under `X`.
Composition of the two actual algebraically finite étale bounded maps
proves that the new structural map lies in the required subcategory.
No target algebra, norm or action is chosen.

The object and arrow formulas identify the unchanged target action and
the original equivariant and bounded arrow maps. The new structural
equivariant map is `f ≫ W.baseHom`; its bounded algebra map is
`W.baseMap.comp (NormContinuousAffinoidAction.homMap f)`. The functor is
faithful because equality of the retained bounded maps determines the
original relative arrows.

`reindex_comp_forget` proves equality with the original functor to
target actions. `reindex_comp_forgetAction` identifies precomposition
after forgetting the action with the published non-equivariant
`AlgebraicallyFiniteEtaleAffinoidUnder.reindex`. Both are reflexive
equalities of functors.

`reindexId` and `reindexComp` compare identity and composite
precomposition by natural isomorphisms. Their components retain identity
equivariant maps of the target algebras. The identity comparison lifts
Mathlib's `Under.mapId`; the composite comparison uses `Under.isoMk`
and the identity and associativity laws. Naturality follows by
extensionality of the retained bounded maps.

## Existing bounded equivariant base isomorphisms

`NormContinuousAffinoidAction.iso_hom_algebraicallyFiniteEtale e` applies
the published bounded-base-isomorphism lemma to the isomorphism obtained
by forgetting the action. Both inverse bounded maps are already part of
`e : X ≅ Y`; an algebraically bijective bounded map alone is not used to
construct an inverse.

`transport e` is precomposition by `e.hom`, with the same explicit
structural-map and arrow-map formulas. `transportUnit` and
`transportCounit` lift the actual unit and counit of Mathlib's
`Under.mapIso e` to the full finite étale subcategories. Their maps are
identities on the unchanged target actions. `transportEquivalence e`
has exactly `transport e` and `transport e.symm` as functor and inverse;
the triangle identity follows from relative bounded-map extensionality.

## Continuous spectra over the base

Assume additionally that `G` is a topological group. The published
spectrum construction then gives actual jointly continuous actions and
continuous equivariant seminorm pullbacks.
`reindex_op_comp_spectrumFunctor` proves that forgetting the geometric
base after precomposition retains exactly the original spectrum functor.

`spectrumReindexIso f hf` compares the spectrum over `X` of the
precomposed structural arrow with the original spectrum over `Y`
followed by `Over.map` of the actual map `M(Y) → M(X)`. The base map is
`NormContinuousAffinoidAction.spectrumFunctor.map f.op`, so the two
functors have the same target over `M(X)`.

Each component is the identity equivariant homeomorphism of the actual
spectrum of `B`. Its commuting triangle evaluates at a seminorm `x`
and `a ∈ X` to the same value `x (W.baseMap (f(a)))`. Extensionality of
the full action category, action maps, continuous maps and seminorms
proves the triangle; naturality reduces to identical point maps.
The two evaluation lemmas explicitly identify the forward and inverse
component maps with the identity. Continuity is inherited from the
published spectrum functors and the identity isomorphism.

As in the imported modules, the spectrum section installs the published
`NormContinuousAffinoidAction.topCatSelfForget` locally to spell
Mathlib's continuous actions on `TopCat`.

## Sources, provenance and scope

Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
Definition 3.3.1(i), printed/PDF p. 17, defines finite affinoid morphisms
using finite Banach algebras. Definition 3.3.9(i), p. 19, defines finite
étaleness by algebraic finite étaleness on every affinoid domain.
The registered source is `berkovich-2009-trieste-analytic-spaces`,
PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
at https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.

The exact equivariant precomposition, equivalence and spectrum
comparison are internal constructions from the published actual
norm-continuous action category, finite étale undercategory and
non-equivariant base transport, with Mathlib's undercategory and
overcategory operations. They are not attributed as numbered assertions
of the lectures.

This composes structural maps along an existing algebraically finite
étale base arrow. It does not construct tensor base change or prove
analytic étaleness on all affinoid domains. The ground field and acting
group are retained. Analytic automorphism topology, atlases, coverings,
and full equivariant analytic sites remain separate obligations.
Trivial valuations, zero quotients and empty spectra remain allowed.
