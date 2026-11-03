# Morphism presheaves under fully faithful strong transformations

This is an internal construction from Mathlib's actual `Pseudofunctor.StrongTrans`,
`Functor.FullyFaithful`, `Pseudofunctor.presheafHom` and coherent `pullHom`, and
the published `PseudofunctorPointFiberTransport` data `component`, `comparison`
and `comparison_comp`. It is the morphism analogue of the isomorphism transport in
`PseudofunctorPointFiberTransport`. The base category, base morphisms, fibre
objects and fibre morphisms retain four independent universe parameters. No
geometric existence or representability result is used.

Let `α` be a strong transformation from a contravariant category-valued
pseudofunctor `F` to `G` on the same category `C`. For actual objects `ξ` over `U`
and `η` over `T`, base maps `a : Z → U` and `p : Z → T`, and an actual fibre
morphism `φ : F(a) ξ ⟶ F(p) η`, `transportHom` is

```
(comparison α a ξ).inv ≫ (component α Z).map φ ≫ (comparison α p η).hom,
```

an actual morphism `G(a) (component α U ξ) ⟶ G(p) (component α T η)`.

`transportHom_pullHom` proves that this transport commutes with Mathlib's
coherent pullback `pullHom` along any `q : Z' → Z`, for arbitrary prescribed
composites `qa = q ≫ a` and `qp = q ≫ p`. The proof substitutes the two
composites, expands `comparison_comp` and `pullHom` into the composition
comparisons of `F` and `G`, cancels the two adjacent images under
`component α Z'` of the inverse and forward composition comparisons of `F`
(at `ξ` and at `η`), and finishes with the naturality of the
strong-transformation comparison `α.naturality q` at the morphism `φ`.

For objects `M` and `N` over the same `S`, `presheafHomMap` is the resulting
natural transformation

```
F.presheafHom M N ⟶ G.presheafHom (component α S M) (component α S N)
```

on the entire slice `Over S`; at `Z` it applies `transportHom` with both base maps
equal to the structure map of `Z`. Its naturality on every slice morphism is
`transportHom_pullHom`. No full-faithfulness hypothesis is needed for this map.

If every `component α Z` is fully faithful, `presheafHomEquiv` is a bijection on
each value: it composes the fully faithful functor's bijection on morphisms with
conjugation by the two comparison isomorphisms (a private helper
`homConjugationEquiv`). `presheafHomEquiv_apply` records that its forward map is
exactly `transportHom`. `presheafHomIso` assembles these bijections into a
natural isomorphism of the full Hom presheaves, with all restriction maps, and
`presheafHomIso_hom` records that its forward map is `presheafHomMap`.
Full faithfulness is required in every fibre. No essential surjectivity is
assumed: the comparison concerns objects in the image of the transformation.

This module constructs comparisons of presheaves only. It asserts no
representability, no stack property and no atlas existence.

`presheafHomIso_hom_app_apply` records that the forward component at a slice
object is exactly `transportHom` applied to its structure map twice. It is the
componentwise form of `presheafHomIso_hom`. The comparison and its component
formula share the `PseudofunctorPresheafHomTransport` namespace.
