# The actual source-subatlas Hom quotient and its colimit property

This is an internal construction from the already constructed saturated
strong-map category and its localization. Its inputs are actual refining
original-chart subatlases, complete strong restriction maps, every-arrow
source-subatlas representation, and exact common-source equality. No new
original-literature attribution is made. The derivation below explains the
provenance of the construction and its proofs.

## Objects, hypotheses and sizes

Let `K : Type u` be a complete ultrametric normed field, and let `A` and `B`
be saturated atlas presentations with ambient spaces in universe `v` and
original chart indices in universe `w`. The three universes are independent.
Every morphism is an actual complete strong map: it retains its continuous
ambient map and a bounded algebra pullback at every admissible chart pair.
The original saturation hypothesis contains all local full affinoid domains.

The type `A.presentation.atlas.RefiningSelection` consists of downward-closed
sets of original chart indices with the proved finite relative local-refinement
condition. For a selection `P`, write `A_P` for the constructed saturated
`A.refiningSubpresentation P` on the literal ambient space of `A`, and `i_P`
for its canonical full quasi-isomorphism inclusion in `A`.

`SourceHomRepresentative A B` is the dependent sum of these selections and
the actual strong Hom types `A_P ⟶ B`. Its universe is `max u v w`.
`sourceHomRepresentativeMap` interprets `(P,f)` as the existing localized
right fraction with denominator `i_P` and numerator `f`. The original
localization may have a larger Hom universe because its paths range over
intermediate objects; the equivalence below permits this size difference.

## Exact quotient and localization comparison

`sourceHomSetoid A B` relates `(P,f)` and `(Q,g)` exactly when
`HasCommonSourceRefinement f g` holds. This predicate supplies an actual
refining selection `R`, containments `R ≤ P` and `R ≤ Q`, and equality of
the entire strong restrictions on `A_R`. Its reflexivity, symmetry and
transitivity follow by the proved `localizedSourceRefinement_eq_iff`,
which identifies the predicate with equality of the interpreted localized
arrows. Thus the equivalence relation is derived from exact complete-map
equality; an equivalence relation is not assumed as extra geometry.

`SourceHomQuotient A B` is the quotient by this setoid.
`sourceHomι P f` inserts an actual complete numerator. The theorem
`sourceHomι_eq_iff` states that two inserted numerators are equal in this
quotient exactly when they have such a common original-chart source.

For `h : P ≤ Q`, `refiningHomRestriction h f` is precomposition with the
constructed complete selection map `A_P ⟶ A_Q`. The theorem
`sourceHomι_restriction` proves

```text
sourceHomι P (refiningHomRestriction h f) = sourceHomι Q f.
```

The witness is the actual selection `P` with its identity containment and
the given containment in `Q`; the restriction identity law proves the full
numerator equation.

`sourceHomQuotientMap` descends interpretation to the quotient. The
component formula is `sourceHomQuotientMap_ι`. Its injectivity follows by
quotient induction and the exact common-source equality criterion. Its
surjectivity follows from `exists_sourceRefinementFraction`: every arrow
of the existing localization has an actual strong numerator on a refining
original-chart source subatlas. These prove
`sourceHomQuotientMap_bijective` and construct `sourceHomEquiv`.
`sourceHomEquiv_ι` records its value on each component.

`localizedSpaceFunctor_map_sourceHomEquiv_ι` computes the underlying
continuous map of the interpreted class: it is exactly `TopCat.ofHom
f.baseMap`. This uses the previously proved formula for the canonical
same-space inclusion fraction. It makes no assertion that continuous
maps determine bounded pullbacks.

## Descent to an independently sized type

For an arbitrary `Z : Type z`, with `z` independent of `u`, `v` and `w`,
`SourceHomCompatible φ : Prop` says that a family of functions

```text
φ P : (A_P ⟶ B) → Z
```

satisfies `φ P (refiningHomRestriction h f) = φ Q f` for every `P ≤ Q`
and every actual numerator `f` on `Q`.

`sourceHomDesc φ hφ` constructs the function from `SourceHomQuotient A B`
to `Z` by quotient lift. To prove well-definedness, take the witnessed
common source `R`. Compatibility identifies each original family value
with its value after restriction to `R`; the complete numerator equality
identifies those two restricted values. No injectivity of restriction is
needed. `sourceHomDesc_ι` gives the representative formula.
`sourceHomDesc_unique` proves that every function with these representative
values equals the constructed descent, by function extensionality and
quotient induction.

## The actual filtered Hom diagram and categorical colimit

`sourceHomDiagram A B` has index the opposite of the inclusion category
of refining selections and values in `Type (max u v w)`. It is explicitly
the opposite of `refiningSubatlasFunctor A` composed with `yoneda.obj B`.
Thus its value at `op P` is the actual complete strong Hom type
`A_P ⟶ B`. For `P ≤ Q`, its map from `op Q` to `op P` is exactly
`refiningHomRestriction h`, as recorded by `sourceHomDiagram_map`.

`sourceHomDiagram_index_filtered` proves that this index is filtered:
the inclusion order is cofiltered because selections have their constructed
intersection and a top selection. The existing order-category instances
give filteredness of its opposite. This uses actual refining selections,
including their local-refinement proofs.

`sourceHomCocone A B` has vertex `SourceHomQuotient A B` and components
`sourceHomι`. Its naturality equation is the proved restriction formula.
`sourceHomCocone_compatible` extracts a compatible family from any cocone
by evaluating its naturality equation on each actual numerator.

`sourceHomIsColimit A B` constructs a categorical `IsColimit` witness.
Its universal map to any cocone is `sourceHomDesc` on that cocone's family.
Factorization is the representative formula. Uniqueness is
`sourceHomDesc_unique`, with the competing map's component equations
evaluated on the actual numerators. Consequently the actual source Hom
diagram has this quotient as its colimit, and `sourceHomEquiv` identifies
that quotient with the existing localization Hom type.

## Scope

This unit constructs the exact source-subatlas Hom quotient, its localization
Hom equivalence, descent to independently sized types and the categorical
filtered-colimit witness. It does not prove injectivity of restriction
transitions or faithfulness of the localization. Analytic identification
with a separately defined category, actual analytic etale, quasi-etale and
equivariant sites, compact/distinguished domains and Harris tower
specializations remain obligations of the surrounding task. Every
predecessor retains its independent acceptance and publication gate.
