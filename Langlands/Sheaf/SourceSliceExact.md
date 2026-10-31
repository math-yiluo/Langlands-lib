# Exact source changes for diagrams on slice sites

Author: Worker 13.

This internal categorical prerequisite proves additivity and finite-limit and
finite-colimit preservation for the actual functors in
[SourceSlice](SourceSlice.md). It constructs no new geometric comparison.
The six object and hom universes of the site, coefficients and index category
remain independent, with the same notation `J`, `A`, `I` and `Y : I ⥤ C`.

## Provenance

The preservation argument uses the proved slice restriction properties in
[SliceMap](SliceMap.md) and [SliceExact](SliceExact.md), followed by Mathlib's
pointwise whiskering preservation instances. The latter are in
`Mathlib/CategoryTheory/Limits/Preserves/FunctorCategory.lean` at the pinned
commit `5ed2965256430c3649e86755f9576b54eca72435`.
Additivity uses the sheaf category's inherited preadditive structure and the
instances in `Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean`.
This is a derived internal construction, with no new literature assertion.

## Additivity

When `A` is preadditive, `overMapPullback_additive` and
`overPullback_additive` prove that both actual slice restriction functors
preserve addition of morphisms. On every section the equality is reflexive:
restriction retains the original morphism component and sectionwise addition.
Consequently `sourceSliceRestriction`, `sourceSliceReindex` and
`sourceSliceDiagramFunctor` are additive. The first is postcomposition by
slice restriction, the second precomposition by `Under.map f`, and the third
precomposition by `Under.forget k` followed by global-to-slice restriction.

## Finite preservation

For `f : k → l`, the instances assert:

- `sourceSliceRestriction J A Y f` preserves finite limits if `A` has finite
  limits. It preserves finite colimits if `C` has pullbacks and
  `Sheaf (J.over (Y.obj l)) A` has finite colimits.
- `sourceSliceReindex J A Y f` preserves finite limits if `A` has finite
  limits. It preserves finite colimits if
  `Sheaf (J.over (Y.obj k)) A` has finite colimits.
- `sourceSliceDiagramFunctor J A Y k` preserves finite limits if `C` has
  binary products and `A` has finite limits. It preserves finite colimits
  if `C` has binary products and `Sheaf J A` has finite colimits.

For each finite shape, restriction between slices preserves limits by
SliceMap. With pullbacks in `C`, its sheaf adjunction makes it preserve
colimits. Global restriction uses SliceExact's corresponding preservation
results, including its binary-product premise. The source sheaf categories
have the needed finite limits when `A` does. Finite colimit existence is
retained explicitly as stated above. Mathlib then transfers preservation to
postcomposition and precomposition of entire diagrams, and to their composite.

If the sheaf categories are abelian and `A` is preadditive with finite limits,
these are additive exact functors under the stated colimit and site premises.
The instances do not assert abelianness or supply missing colimits. In the
small-etale module application, sheafification on each actual induced slice
supplies the relevant abelian categories.

## Complex comparison

For any `ι : Type uN` and `c : ComplexShape ι`, with `A` preadditive,
`sourceSliceComplexChangeIso` compares termwise localization at `l` followed
by termwise restriction with termwise localization at `k` followed by
termwise reindexing. Its domain is `HomologicalComplex (I ⥤ Sheaf J A) c`;
its target consists of complexes in the entire mixed diagram category
`Under l ⥤ Sheaf (J.over (Y.obj k)) A`. The shape universe is independent.

The isomorphism is `NatIso.mapHomologicalComplex` of the actual
`sourceSliceChangeFunctorIso`. The composition formulas for termwise functors
are definitionally the corresponding composites. Its component in degree `q`
is `sourceSliceChangeIso` at `K.X q`, by reflexivity. At every index and slice
section, its forward map is the identity, also by reflexivity. Naturality,
invertibility and compatibility with differentials come from the original
natural isomorphism and Mathlib's homological-complex construction. This
comparison needs only preadditivity, independently of the preservation premises.

## Scope

No covering, torsor, filtering, cofinality or chosen derived localization is
assumed. The functors retain whole `Under` diagrams and their transitions.
This file constructs neither derived categories nor cohomology or Harris
geometry; it prepares the existing functors for those applications.
All intrinsic preservation obligations are proved without new axioms or holes.
