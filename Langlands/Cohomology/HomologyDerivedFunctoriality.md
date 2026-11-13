# Functoriality of the canonical Hom-cohomology localization map

This is an internal construction supporting the comparison between relative
module cohomology and arbitrary sheaf-cohomology pullback. It uses the published
`EquivariantComposite.homologyDerivedMap`, the Hom-complex constructions in
Mathlib, and Mathlib's derived-category functor for an exact additive functor.
There is no separate literature assertion being transcribed.

Let `C` and `D` be abelian categories with the same morphism universe, let
`F : C ⥤ D` be additive, let `X : C`, and let `a : Y ⟶ F.obj X`.
For an integer-indexed cochain complex `K` in `C`,
`homComplexMap F a K` is the chain map

```text
Hom_C(X, K) → Hom_D(Y, F(K))
```

whose degree `i` component sends `b` to `a ≫ F.map b`. Additivity of `F`
proves additivity of each component, and preservation of composition proves the
chain-map equation. No exactness assumption is used in this definition.

The supporting lemmas are:

- `homologyDerivedMap_homologyπ`: on the homology class of an actual cycle, the
  canonical comparison is localization of the shifted chain map of that cycle.
- `map_fromSingleMk`: the shifted chain map of a cycle commutes with any
  additive functor, after the usual comparison for complexes concentrated in
  degree zero.
- `homologyDerivedMap_map`: if `F` also preserves finite limits and finite
  colimits, applying `homComplexMap` on cohomology agrees with applying
  `F.mapDerivedCategory` to the canonical derived morphism, followed by the
  derived-category factorization isomorphism and preceded by `a` and the
  degree-zero comparison isomorphism.

The last lemma applies to arbitrary complexes. It has no assumptions about
injective objects, K-injectivity, boundedness, or acyclic terms. This distinction
is needed because an exact inverse-image functor on abelian sheaves need not
preserve injectives.

The proof first lifts a cohomology class to a cycle using the epimorphism from
cycles to homology. Naturality of the homology projection identifies the mapped
cycle. The explicit single-complex cocycle formulas handle precomposition by
`a` and application of `F`. Naturality of
`F.mapDerivedCategoryFactors.hom` then identifies the two localized shifted
morphisms. This module supplies a supporting construction and its laws; it
does not yet prove the target relative module/sheaf comparison.
