# Structural-base transport of relative finite étale generalized actions

Authors: Worker 56 and Worker 36. This internal derived construction adapts
Worker 36's published strict `EquivariantFiniteEtaleTransport` to the actual
positive-polyradius quotients and their norm-continuous actions. All new
declarations lie in `Langlands.Analytic.PresentedAffinoidAlgebra`.

Let `K` be an ultrametric normed field and `G` a group with a topology,
in independent universes. An action object has an actual quotient of a finite
positive-polyradius restricted-series algebra by a closed ideal, with its
quotient norm and continuous forward orbits of algebra elements. Neither
completeness of `K` nor continuity of the group operations is required for
the algebraic category. Trivial valuations, zero quotients, zero presentation
arity, and empty spectra remain allowed.

## Structural precomposition

For an equivariant bounded map `f : X ⟶ Y` whose underlying ring map is
algebraically finite étale, `AlgebraicallyFiniteEtaleActionUnder.reindex f hf`
takes a structural arrow `Y → B` to `X → Y → B`. The functor includes the
existing full relative category in `Under Y`, applies Mathlib's actual
`Under.map f`, and lifts to the full finite étale subcategory of `Under X`.
Composition of the actual finite étale structural maps proves the required
object property. The target quotient algebra, norm, action, and every bounded
equivariant relative arrow are retained.

The object and arrow formulas expose this behavior:

| Declaration | Retained data or resulting formula |
| --- | --- |
| `reindex_obj_right` | The original target action |
| `reindex_obj_baseHom` | `f ≫ W.baseHom` |
| `reindex_obj_baseMap` | `W.baseMap.comp (NormContinuousAction.homMap f)` |
| `reindex_map_homAction` | The original equivariant arrow |
| `reindex_map_homMap` | The original bounded algebra map |

Equality of the retained bounded maps determines equality of the original
relative arrows, proving faithfulness. `reindex_comp_forget` is a reflexive
equality with the original functor to target actions.
`reindex_comp_forgetAction` is a reflexive equality with the generalized
non-equivariant `AlgebraicallyFiniteEtaleUnder.reindex` after forgetting
actions. Both equalities concern the complete functors.

`reindexId` lifts Mathlib's `Under.mapId` to the full subcategory.
`reindexComp` compares precomposition by a composite with successive
precomposition. Its components use identity equivariant maps on the targets;
associativity proves their structural triangles. Relative bounded-map
extensionality proves naturality of both comparisons.

## Existing bounded equivariant base isomorphisms

`NormContinuousAction.iso_hom_algebraicallyFiniteEtale e` forgets the action
of `e : X ≅ Y` and applies the generalized bounded-base-isomorphism lemma.
Both bounded inverse maps already belong to the isomorphism. That lemma
evaluates their two inverse identities to prove bijectivity, then applies the
published finite-étale property of a bijective ring map. No bounded inverse is
inferred from algebraic bijectivity alone.

`transport e` is precomposition by `e.hom`. The two evaluation lemmas identify
its structural bounded map and its unchanged bounded arrow map.
`transportUnit` and `transportCounit` lift the actual unit and counit of
Mathlib's `Under.mapIso e` to the full finite étale subcategories. Their
components are identity maps on the retained target actions.
`transportEquivalence e` has exactly `transport e` and `transport e.symm`
as functor and inverse. Relative bounded-map extensionality proves its
triangle identity.

## Continuous equivariant spectra over the base

Assume additionally that `G` is a topological group. The existing spectrum
functor then constructs actual jointly continuous actions by inverse pullback
on bounded multiplicative seminorms. Its continuity is derived from continuous
algebra-element orbits. `reindex_op_comp_spectrumFunctor` is a reflexive
equality: precomposition retains the original target continuous spectra and
their equivariant pullback maps.

`spectrumReindexIso f hf` compares the relative spectrum after precomposition
with the original relative spectrum followed by `Over.map` of
`NormContinuousAction.spectrumFunctor.map f.op`. This is the actual
contravariant base spectrum map `M(Y) → M(X)`, so both functors land over
`M(X)` in `ContAction TopCat G`.

Each component is the identity equivariant homeomorphism of the actual
spectrum `M(B)`. For a seminorm `x` and `a ∈ X`, its structural triangle
evaluates on both sides to `x (W.baseMap (f(a)))`. Extensionality of the full
continuous-action category, action maps, continuous maps, and seminorms proves
the triangle. Naturality reduces to equality of the same point maps.
`spectrumReindexIso_hom_apply` and `spectrumReindexIso_inv_apply` both state
that the component map sends `x` to `x`. The identity isomorphism and existing
spectrum functors provide continuity and equivariance.

As in the imported generalized action modules, the spectrum section installs
`Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget` locally.
This is the shared identity forgetful functor on `TopCat`, retaining the
actual spectrum topology.

## Sources, provenance, and scope

Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
Definition 3.3.1(i), printed/PDF p.17, defines finite affinoid morphisms through
finite Banach algebras. Definition 3.3.9(i), printed/PDF p.19, requires
algebraic finite étaleness over every affinoid domain for finite étale analytic
morphisms. Registered original: `berkovich-2009-trieste-analytic-spaces`,
PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
at https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.

These passages motivate the narrower algebraic prerequisite. The exact
equivariant structural precomposition, bounded-base equivalence, and spectrum
comparison are internally derived from the actual generalized action category,
its finite étale full undercategory, the generalized non-equivariant transport,
and Mathlib's undercategory and overcategory operations. The strict transport
supplies the credited proof pattern. No target algebra, norm, action, inverse,
output comparison, or desired continuity result is postulated. These exact
constructions are not attributed as numbered assertions of the source.

This composes structural algebra maps along an existing finite étale arrow.
It constructs no tensor product or geometric fiber product, and proves no
analytic étaleness on every affinoid domain. The coefficient field and acting
group are retained. Analytic automorphism topology, atlases, coverings, and
equivariant analytic sites remain separate obligations. Over an incomplete
field the objects retain their normed-quotient meaning; identification with
complete affinoid analytic spaces is not asserted.
