# Decomposition groups acting on isotypic parts and multiplicity spaces

This internal construction combines the decomposition-group restriction of
`Langlands.Shimura.DecompositionGroupAction` with the isotypic parts and
multiplicity spaces of `Langlands.Shimura.IsotypicGaloisAction`. Mapping an
action through a functor preserves unramifiedness at a finite place and
sends the geometric Frobenius endomorphism to its image. For a
representation `τ`, restriction to the decomposition group at `v` commutes
with taking `τ`-isotypic parts. The Frobenius endomorphism of the isotypic
part is the restriction of the ambient Frobenius endomorphism. Evaluation
`τ ⊗ Hom_G(τ, X) → X[τ]` intertwines the Frobenius endomorphisms of the
multiplicity space and of the isotypic part. The declarations are in
namespace `Langlands.Shimura.IsotypicDecompositionAction`. The exceptions are
`IsUnramifiedAlong.mapAction`, `IsUnramifiedAlong.isotypic` and
`IsUnramifiedAlong.multiplicity`, which are in namespace
`Langlands.Shimura.DecompositionGroupAction` so that they can be used with
dot notation on `IsUnramifiedAlong`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313 has two relevant parts. Part (iii)
describes the action of the decomposition group `Z_w = Gal(F̄_w/F_w)` on
the isotypic component `H^{n-1}(S_K(N), W)[π]`. Part (ii) uses the
Frobenius eigenvalues at almost all unramified places, through formula
(5.6). This module provides the decomposition group action, unramifiedness
and Frobenius endomorphisms on isotypic parts and multiplicity spaces of
smooth representations with a commuting Galois action.

No unramifiedness of any particular action is proved; the results about
unramified actions take it as a hypothesis. `τ` is any `R`-linear
representation. No topology on the Galois groups and no continuity of
actions is considered. No statement of Harris is formalized.

## Inputs

Let `K` be a number field and `v : Global.FinitePlace K`. Closure
embeddings `ι` are elements of
`ClosureEmbedding (NumberField.FinitePlace.embedding v)`.

The module `Langlands.Shimura.DecompositionGroupAction` (candidate
`24e3f602-b5d7-4c07-8a1d-4d8b67948758`, accepted and awaiting publication)
provides `localRestriction v ι`, the restriction functor
`atFinitePlace V v ι`, `mapActionResIso`, the predicate
`IsUnramifiedAlong V v M ι` (every element of the actual inertia subgroup
`localInertia v` acts by the identity after restriction), the Frobenius
endomorphism `geometricFrobenius V v M ι` (the action of the chosen lift
`geometricFrobeniusLift v` after restriction), and
`geometricFrobenius_naturality`.

The module `Langlands.Shimura.IsotypicGaloisAction` (candidate
`06482d9c-709f-449e-bd42-538102e24d51`, staged) provides `isotypicObj`,
`isotypicMap`, `isotypicFunctor`, `isotypicι`, `isotypicActionFunctor`,
`isotypicActionι`, `multiplicityFunctor`, `multiplicityActionFunctor`,
`multiplicityRepresentation`, `isotypicEvaluation` and
`isotypicEvaluation_galois`.

## Mapping actions through a functor

Let `F : V ⥤ W` be a functor between categories, with possibly different
universe levels, and let `M` be an object of
`Action V (Field.absoluteGaloisGroup K)`.

- `IsUnramifiedAlong.mapAction F hM`: if `M` is unramified at `v` along `ι`,
  so is `(F.mapAction _).obj M`, because inertia acts by `F.map (𝟙 _)`.
- `geometricFrobenius_mapAction F M ι`: the Frobenius endomorphism of
  `(F.mapAction _).obj M` is `F.map (geometricFrobenius V v M ι)`, by `rfl`.

## Isotypic parts and multiplicity spaces

Let `R` be a commutative ring, `G` a group with a topology,
`τ : Representation R G U`, and `X` an object of
`Action (SmoothRep R G) (Field.absoluteGaloisGroup K)`.

- `isotypicAtFinitePlaceIso v τ ι` is the natural isomorphism from
  `isotypicActionFunctor τ (Field.absoluteGaloisGroup K)` followed by
  `atFinitePlace _ v ι` to `atFinitePlace _ v ι` followed by
  `isotypicActionFunctor τ (LocalGroup v)`. It is `mapActionResIso` for
  `isotypicFunctor τ`, and its components are identities
  (`isotypicAtFinitePlaceIso_hom_app_hom`).
- `IsUnramifiedAlong.isotypic τ hX`: if `X` is unramified at `v` along `ι`,
  so is its `τ`-isotypic part `(isotypicActionFunctor τ _).obj X`.
- `isotypic_geometricFrobenius τ X ι`: the Frobenius endomorphism of the
  isotypic part is `isotypicMap τ (geometricFrobenius _ v X ι)`, by `rfl`.
- `geometricFrobenius_isotypicι τ X ι`: the inclusion
  `(isotypicι τ).app X.V` intertwines the Frobenius endomorphisms of the
  isotypic part and of `X`. It is `geometricFrobenius_naturality` for the
  component of `isotypicActionι`.
- `multiplicityRepresentation_atFinitePlace τ X ι g`: an element `g` of
  `LocalGroup v` acts on the multiplicity space of the restricted action as
  `localRestriction v ι g` acts on that of `X`, by `rfl`.
- `IsUnramifiedAlong.multiplicity τ hX`: if `X` is unramified at `v` along
  `ι`, so is `(multiplicityActionFunctor τ _).obj X`.
- `isotypicEvaluation_geometricFrobenius τ X ι`: as linear maps,
  `isotypicEvaluation τ X.V` composed with `LinearMap.lTensor U` of the
  Frobenius endomorphism of the multiplicity space equals the Frobenius
  endomorphism of the isotypic part composed with `isotypicEvaluation τ X.V`.
  It is `isotypicEvaluation_galois` at
  `localRestriction v ι (geometricFrobeniusLift v)`.

## Proof outline

Unramifiedness of mapped actions follows from `F.map_id`. The
isomorphism is `mapActionResIso`. The descriptions of Frobenius
endomorphisms and of restricted multiplicity representations hold by
`rfl`. The intertwining results are `geometricFrobenius_naturality` and
`isotypicEvaluation_galois`.

## Provenance

This is an internal construction combining
`Langlands.Shimura.DecompositionGroupAction` and
`Langlands.Shimura.IsotypicGaloisAction`. Harris (1999), Theorem 5.7 (ii),
(iii) and formula (5.6) on printed p. 313, is motivation only.
