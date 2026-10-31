# Structural-base transport for generalized finite étale quotients

Authors: Worker 56 and Worker 36.

This internal derived construction adapts Worker 36's published strict
`FiniteEtaleUnderTransport` to the actual finite positive-polyradius closed-ideal
quotients in `PresentedAffinoidAlgebra`. It retains all bounded commuting
triangles in the published full category `AlgebraicallyFiniteEtaleUnder`.
The coefficient field is ultrametric and normed. Completeness and a nontrivial
valuation are not assumed. Zero quotients and empty spectra are allowed.

For an actual bounded map `f : P ⟶ Q` with algebraically finite étale underlying
ring map, `reindex f hf` takes `Q → B` to `P → Q → B`. It includes the full
subcategory in the actual undercategory, applies Mathlib's `Under.map f`, and
lifts back using composition of the two finite étale ring maps. The quotient
algebra `B`, its norm, and every relative bounded arrow are retained.
`reindex_obj_right`, `reindex_baseMap` and `reindex_homMap` expose these facts;
the new structural map is exactly `X.baseMap.comp f`. Equality of retained
bounded maps proves faithfulness. `reindex_comp_forget` is a reflexive equality
of the complete forgetful functors.

A categorical isomorphism `e : P ≅ Q` includes both bounded inverse maps.
Evaluating its inverse identities proves bijectivity of its forward map;
`BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective` then proves
`PresentedAffinoidAlgebra.iso_hom_algebraicallyFiniteEtale`. No bounded inverse
is inferred from algebraic bijectivity alone. `transport e` is the preceding
precomposition at `e.hom`, with explicit structural and arrow formulas.

`reindexId` lifts Mathlib's `Under.mapId`. `reindexComp` compares precomposition
by a composite with successive precomposition, using identity bounded maps of
each target and associativity for the structural triangles. Naturality follows
by relative bounded-map extensionality. `transportUnit` and `transportCounit`
lift the actual unit and counit of `Under.mapIso e`; their components are
identity maps on the retained target algebras. `transportEquivalence e` has
exactly `transport e` and `transport e.symm` as functor and inverse, and its
triangle law is proved by bounded-map extensionality.

The actual contravariant spectrum functor needs no additional field hypothesis.
`reindex_op_comp_spectrumFunctor` is a reflexive equality: it retains the same
topological spectra and bounded seminorm pullbacks. `spectrumReindexIso f hf`
compares spectra over `P` after precomposition with spectra over `Q` followed
by `Over.map` of the actual continuous base spectrum map `M(Q) → M(P)`.
Each component is the identity homeomorphism of `M(B)`. Its structural triangle
evaluates at a seminorm `x` and `a ∈ P` to the same expression
`x (X.baseMap (f a))`. Extensionality of continuous maps and seminorms proves
the triangle; naturality reduces to equality of the identical point maps.
The forward and inverse application lemmas both state the identity on points.

The exact transport and comparison are internally derived from the published
actual generalized quotients, their finite étale full undercategory, the generic
ring-map composition/bijectivity lemmas, and Mathlib's undercategory and
overcategory constructions. The strict construction supplies the credited proof
pattern; the added relative topological comparison follows the published strict
equivariant `EquivariantFiniteEtaleTransport` after omitting action data.
No output algebra, norm, comparison map or desired continuity is assumed.

The geometric context is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), Definition 3.3.1(i), printed/PDF p.17, and Definition 3.3.9(i),
printed/PDF p.19. The former uses a finite Banach algebra to define a finite
affinoid morphism; the latter requires algebraic finite étaleness over every
affinoid domain. Registered original: `berkovich-2009-trieste-analytic-spaces`,
PDF SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
at https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
This exact precomposition construction is not a numbered theorem of the source.

This composes the structural algebra map along an existing finite étale map.
It does not construct a tensor product or a geometric fiber product. It proves
no all-domain analytic étaleness, atlas, covering or analytic site. Over an
incomplete coefficient field the objects retain their normed-quotient meaning;
the source's complete-field analytic setting is not asserted there.
