# Point fibres of a pseudofunctor reindexed along a left adjoint

Namespace: `Langlands.CategoryTheory.PseudofunctorPointFiberReindex`.

This is internal categorical infrastructure built on the published
`PseudofunctorPointFiber`, `PseudofunctorPointFiberAtlasRestriction` and
`StackPullback` modules. It introduces no new literature assertion.

## Setting

Let `C` and `D` be categories with the same morphism universe `v`, let
`Φ : C ⥤ D` be a functor and let `P : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat` be a
category-valued pseudofunctor. `StackPullback.reindex Φ P` is the composite
pseudofunctor `Φ.op.toPseudofunctor.comp P` on `C`. For `ξ` over `U` and a
test object `η` over `T`, a point of the actual fibre over `Z : Over T` is a
pair `⟨a, e⟩` of an actual map `a : Z.left ⟶ U` and an actual isomorphism
`e : a^* ξ ≅ (Z.hom)^* η` (published `PseudofunctorPointFiber.Points`).
The common morphism universe is needed so that both point-fibre presheaves
take values in the same universe of types.

## Applying `Φ` to base maps

- `pullIso_reindex` identifies the coherent pullback of isomorphisms for the
  reindexed pseudofunctor with coherent pullback for `P` along the image
  arrows. It is the isomorphism version of the published `pullHom_reindex`.
- `mapPoints Φ P ξ η Z` sends `⟨a, e⟩` to `⟨Φ.map a, e⟩`, a point of the
  fibre of `P` over `(Over.post Φ).obj Z`. The isomorphism is unchanged; its
  type is definitionally the same.
- `mapPoints_restrict` proves compatibility with restriction along every
  slice morphism `q`, using `pullIso_reindex` and `Φ.map_comp`.
- `presheafMap` is the resulting natural transformation
  `presheaf (reindex Φ P) ξ η ⟶ (Over.post Φ).op ⋙ presheaf P ξ η`.

## The adjunction case

Now let `adj : Φ ⊣ Ψ`, `V : D` and `ζ` an object of `P` over `V`.

- `counitObj P adj ζ` is `ζ` pulled back along the counit
  `adj.counit.app V : Φ (Ψ V) ⟶ V`. It is an object of the reindexed
  pseudofunctor over `Ψ V`.
- `adjPoints` composes `mapPoints` with the published atlas-restriction map
  `PseudofunctorPointFiberAtlasRestriction.mapPoints` for the counit. A point
  `⟨a, e⟩` with `a : Z.left ⟶ Ψ V` goes to the point with base map
  `Φ.map a ≫ adj.counit.app V` and isomorphism
  `atlasComparison ≪≫ e`, where `atlasComparison` is the composition
  comparison of `P`.
- `adjPoints_fst` identifies the new base map with the adjoint transpose
  `(adj.homEquiv _ _).symm a`.
- `adjPoints_injective`: equal images have equal transposes, hence equal base
  maps; the isomorphisms then agree after cancelling the comparison.
- `adjPoints_surjective`: every base map `b : Φ Z.left ⟶ V` is
  `Φ.map a ≫ adj.counit.app V` for `a = adj.homEquiv _ _ b`, and the
  isomorphism is recovered by precomposing with the inverse comparison.
- `adjPointsEquiv` is the resulting equivalence of actual point types and
  `adjPoints_restrict` its naturality, inherited from the two natural maps.
- `adjPresheafIso` is the natural isomorphism
  `presheaf (reindex Φ P) (counitObj P adj ζ) η ≅
  (Over.post Φ).op ⋙ presheaf P ζ η` of full point-fibre presheaves.

All isomorphism data are retained; no isomorphism classes are taken. The
geometric application is the comparison of Picard point fibres over a base
change, with `Φ = Over.map s` and `Ψ = Over.pullback s`.
