# Affine neighbourhoods with based coordinate alignment

For affine pinned models `M`, `N`, an arbitrary scheme `T`, a comparison `e`
over `T`, and a supplied coordinate-torus isomorphism `τ`, assume their exact
inclusion square and `PreservesBorel e`. The construction
`affineBasedAlignment e τ hτ hb x` chooses an affine open chart
`q : Spec A ⟶ T` containing each point `x`, together with a
`BasedCoordinateIso`. Its actual group isomorphism is exactly
`pullComparison e q` and its actual torus isomorphism is exactly
`splitTorus.pullIso τ q`. The based root equivalence, standard pairings and
simple-support compatibility come from the existing local alignment, while the
character formula holds on every relative test scheme over `Spec A`.

`AffineBasedAlignment` records the chart, a point above `x`, its open immersion,
the based data, and these two equalities of actual maps.
`affineBasedAlignmentCover` assembles the charts into a
`Scheme.AffineCover @IsOpenImmersion T` indexed by the points of `T`.
No connectedness, quasi-compactness, or nonemptiness assumption is imposed on
`T`; an empty base has an empty indexing type.
`AffineBasedAlignment.preservesCocharacter` proves exact preservation of the
canonical ambient positive-coroot cocharacter on each chosen chart.

This is an internal refinement of `AffinePinnedLocalAlignment`, using
Mathlib's affine open neighbourhood construction and
`HomFamily.ActsBy.comp`:

1. `splitTorus.characters_pullHom_comp` converts a supplied full character
   formula to the corresponding `HomFamily.ActsBy` assertion, restricts it
   along any further morphism, and converts it back. The resulting endpoint
   is the direct normalized pullback along the composite morphism.
2. `exists_affine_basedCoordinateIso` takes a local aligned open `W` containing
   `x`. The theorem `Scheme.exists_affine_mem_range_and_range_subset`
   supplies `q : Spec A ⟶ T` containing `x` with image in `W`. Lifting `q`
   through the open immersion `W.ι` permits restriction of the full character
   formula by the preceding lemma. The based structure is then constructed
   with direct group and torus pullbacks along `q`, using
   `torusSquare_pull` for its exact inclusion square.
3. Classical choice packages this existence as `affineBasedAlignment`.
   The chosen points and their image equalities give the covering condition.
   The cocharacter assertion follows from
   `BasedCoordinateIso.cocharacter_comp` and `groupIso_eq`.

The initial Borel and torus squares are hypotheses. This module supplies
affine charts for a later pinning correction; it does not align pinning
vectors or prove the parent comparison-existence statement.
