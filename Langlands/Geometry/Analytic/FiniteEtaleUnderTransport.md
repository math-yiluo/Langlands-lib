# Finite étale affinoid objects under a bounded base isomorphism

Author: Worker 36.

This derived construction transports the existing category
`AlgebraicallyFiniteEtaleAffinoidUnder Q` along a bounded isomorphism
`e : P ≅ Q` of actual presented strict affinoid algebras. An object with
structural map `Q → B` becomes the same quotient algebra `B`, with structural
map `P → Q → B`. Every compatible bounded arrow is retained. The inverse
transport uses the specified bounded inverse of `e`.

The more general `reindex f hf` restricts Mathlib's actual `Under.map f` to
the published full subcategories, where `hf` proves that the bounded base
map `f` is algebraically finite étale. Composition of finite étale ring maps
proves that the new structural maps lie in the subcategory. There is no
choice of a representing target and no new norm. The formulas
`reindex_baseMap` and `reindex_homMap` identify the constructed structural
map and the unchanged arrows. `reindex_comp_forget` is a definitional
equality with the original forgetful functor.

An isomorphism in the presented-affinoid category includes both bounded
maps. Evaluating its inverse identities proves injectivity and surjectivity
of its forward map. The existing finite-étale-of-bijective-map lemma then
proves `iso_hom_algebraicallyFiniteEtale`. This does not try to obtain a
bounded inverse merely from algebraic bijectivity.

`reindexId` and `reindexComp` compare identity and composite precomposition
with the corresponding functors. Their components are the identity bounded
maps of the unchanged targets; their triangle equations use the category
identity and associativity laws. Naturality follows by equality of the
underlying bounded maps. For an actual bounded base isomorphism,
`transportUnit` and `transportCounit` lift the unit and counit of
Mathlib's `Under.mapIso`. The full-subcategory constructors retain their
underlying commuting triangles. `transportEquivalence` uses these maps
and verifies the triangle identity through the bounded-map extensionality
lemma. The resulting equivalence has exactly `transport e` and
`transport e.symm` as its functor and inverse.

For a complete coefficient field, the opposite reindexing functor followed
by the existing `spectrumFunctor` is definitionally the original spectrum
functor. Thus the target topological spaces and their seminorm-pullback
maps are unchanged as well.

The category and transport allow trivial valuations, zero quotient algebras
and empty presentations. They require an ultrametric normed coefficient
field; completeness is needed only for the spectrum functors. This is a
construction in the existing category of algebraically finite étale
bounded maps. Analytic étaleness on all affinoid domains, general analytic
base change, tensor-product representability, atlases, coverings and
equivariant analytic sites remain separate obligations.

The original source context is Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), Definition 3.3.1(i), printed/PDF p. 17, and
Definition 3.3.9(i), printed/PDF p. 19. These define finite affinoid
morphisms using finite Banach algebras and finite étale morphisms using
algebraic finite étaleness on every affinoid domain. The present transport
is internal algebraic infrastructure for that setting, rather than a
numbered assertion from the lectures. In particular, precomposition here
does not establish the all-domain analytic condition.

The registered original is `berkovich-2009-trieste-analytic-spaces`,
PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
available at
https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
The implemented construction reuses the published `FiniteEtaleUnder`
and `FiniteEtaleAlgebra` modules by Lean name, with Mathlib's pinned
`CategoryTheory.Comma.Over.Basic` and
`CategoryTheory.ObjectProperty.FullSubcategory`.
