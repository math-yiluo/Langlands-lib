# Images of homomorphisms from smooth connected affine groups

`SmoothConnectedHomImageStatement.{u}` says the following for every field `k : Type u`.
Let `A` and `G` be group schemes over `Spec k`, with `A` smooth, connected and affine,
and `G` affine and locally of finite type. Every homomorphism `φ : A ⟶ G` factors as
`fac ≫ inc = φ`. Here `inc : D ⟶ G` is a closed subgroup (`IsClosedSubgroup`), `D` is
smooth, connected and affine over `k`, and the underlying morphism of `fac : A ⟶ D` is
flat, surjective, quasi-compact and locally of finite presentation. The theorem
`smoothConnectedHomImage` proves this proposition.

This is the homomorphism theorem in Milne, *Algebraic Groups*, Theorem 5.39 (printed
p.108), with the image of Proposition 5.46 (printed p.110), for a smooth connected
source. The supporting statement is derived: it records the factorization in the form
used by the split unipotent radical and normal product existence proofs. No hypothesis
on `k` is made.

## Declarations

In namespace `Langlands.GroupScheme.HomImage`, for `φ : A ⟶ G` between affine group
schemes over `Spec k`, with `D := SchematicImage.image φ`, the published schematic-image
group:

- `quasiCompact_hom`: `φ` is quasi-compact, because source and target are affine.
- `isClosedSubgroup_inclusion`: the inclusion `D ⟶ G` is a closed subgroup.
- `projection_w`: the projection `A ⟶ D` commutes with the structure maps.
- `locallyOfFiniteType_image`: if `G` is locally of finite type, so is `D`.
- `geometricallyReduced_image`, `geometricallyIrreducible_image`: if `A` is
  geometrically reduced (resp. irreducible), so is `D`.
- `irreducibleSpace_image`, `connectedSpace_image`: if `A` is geometrically
  irreducible, `D` is irreducible, hence connected.
- `smooth_image`: if `G` is locally of finite type and `A` geometrically reduced,
  `D` is smooth.
- `locallyOfFiniteType_projection`, `locallyOfFinitePresentation_projection`: if `A`
  (and `G`) are locally of finite type, so is the projection, which is then of locally
  finite presentation.
- `flat_projection`: if `A` and `G` are locally of finite type and `A` is
  geometrically reduced, the projection is flat.
- `surjective_projection`: if moreover `A` is geometrically irreducible, the
  projection is surjective.
- `exists_image`: the factorization of the statement, for smooth connected affine `A`.

## Proofs

The schematic image `D`, its closed inclusion and its quasi-compact schematically
dominant projection come from the Library module `SchematicImage`. Since the projection
composed with the structure map of `D` is that of `A`, the Library lemmas
`ImageGeneration.geometricallyReduced_of_isSchemeTheoreticallyDominant` and
`geometricallyIrreducible_of_isSchemeTheoreticallyDominant` carry geometric reducedness
and irreducibility from `A` to `D`. Mathlib's
`GeometricallyIrreducible.irreducibleSpace_of_subsingleton` makes `D` irreducible, so
connected. `D` is locally of finite type as a closed subscheme of `G`; Mathlib's
`smooth_of_grpObj` then makes the geometrically reduced group `D` smooth.

The projection is locally of finite type by cancellation against the structure map of
`D`, and of locally finite presentation since `D` is locally noetherian. `D` is
reduced by `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`. A
quasi-compact schematically dominant morphism is dominant, so the Library's
`DominantHomFlat.flat_of_isDominant` makes the projection flat, and
`DominantHomFlat.surjective_of_flat` makes it surjective onto the irreducible `D`.

For `exists_image`, the Library's `smoothConnectedAffineGeometry` shows that a smooth
connected affine `A` is geometrically integral, hence geometrically reduced and
irreducible. Smooth `A` is locally of finite type, so the lemmas above apply.
