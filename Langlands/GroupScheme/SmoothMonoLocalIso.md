# Smooth group monomorphisms near an isomorphic fibre

This module constructs an open subscheme of an arbitrary base and proves its
isomorphism property for smooth group monomorphisms. It is an internal
prerequisite for the neighbourhood step in
`Langlands.GroupScheme.RelativeParabolicLieContainmentStatement`; it does not
prove that target statement.

## Definitions and conclusions

For a homomorphism `f : H ⟶ K` over `S`, `unitEtaleOpen f` is the inverse image,
under the unit section of `H`, of the scheme etale locus of the underlying
morphism of schemes. Its definition assumes that `H` is locally of finite
presentation over `S` and `K` is locally of finite type over `S`. The helper
`locallyOfFinitePresentation_hom` obtains local finite presentation of `f` by
cancellation from the corresponding structure maps.

`IsIsoNear f s` means that the actual underlying scheme morphism becomes an
isomorphism after base change to some open neighbourhood of `s`.

The main properties are:

- `mem_unitEtaleOpen_of_residueFiber`: if `H` and `K` are smooth over `S`, the
  underlying scheme morphism of `f` is a monomorphism, and its actual residue
  fibre at `s` is an isomorphism, then `s ∈ unitEtaleOpen f`.
- `isIso_unitEtaleOpen`: if `H` and `K` are smooth over `S`, the underlying
  scheme morphism of `f` is a monomorphism, and `K` has geometrically connected
  fibres, then the restriction of `f` to `unitEtaleOpen f` is an isomorphism.
- `isIsoNear_of_residueFiber` combines these two properties.

All these results are universe polymorphic. The base scheme is arbitrary; there
is no affine, quasi-compactness, reduced-base, or noetherian-base assumption.
The isomorphism conclusions concern the underlying scheme morphism of the
actual group-scheme base change.

## Implemented proof

The pointwise helper
`Langlands.AlgebraicGeometry.flat_stalkMap_of_flat_residueFiber` adapts the stalk
proof of the published `Langlands.AlgebraicGeometry.fiberwiseFlatness`: only
flatness of the residue fibre through the chosen source point is used. It
applies the same `fiberStalkFlatness` bridge and `localFiberwiseFlatness` local
algebra criterion. Its source is flat and locally of finite presentation over
the base, and its target is locally of finite presentation over the base.

Apply this helper at the unit over `s`. The isomorphic fibre is flat, so the
stalk map is flat. Monomorphisms are formally unramified. The published local
algebra criterion
`formallyEtale_of_flat_of_formallyUnramified_of_essFinitePresentation`, with
`stalkEssFinitePresentation`, makes this stalk formally etale. This proves
membership in the open defined above.

To prove the isomorphism on that open, let `U` be the etale locus in `H`.
Its structure map to `S` is flat, and `U ⟶ K` is etale by
`etale_schemeEtaleLocus`. After restriction to `unitEtaleOpen f`, the unit gives
a point in `U` over every base point. The implemented proof constructs the
required pullback points explicitly, proving that this family's structure map
is surjective.

The helper `flat_of_flat_family` adapts the commuting-square proof in
`Langlands.GroupScheme.DominantHomFlat.flat_of_isDominant`. A flat family over
the base with surjective structure map replaces the family obtained there by
generic flatness. Its translates cover the source. The shear maps and
`flat_stalkMap_of_comm` from `DominantHomFlat` descend flatness through the
resulting square. Thus the restricted `f` is flat.

Finally `isIso_of_flat` shows that a flat monomorphism locally of finite
presentation onto a smooth group with geometrically connected fibres is an
isomorphism. The flat monomorphism criterion makes it an open immersion. Each
residue fibre of the target is smooth and connected, hence irreducible by
`Langlands.AlgebraicGeometry.irreducibleSpace_of_smooth_connected`.
`DominantHomFlat.surjective_of_flat` gives surjectivity of each fibre
homomorphism. Lifting points through the residue-fibre pullbacks proves
surjectivity of the total morphism. A surjective open immersion is an
isomorphism.

## Provenance

This is a derived internal construction, rather than a transcription of a
separate result from original literature. The proof is assembled from the
published Library results named above and Mathlib's scheme-morphism properties.
The main parabolic containment
statement is used only to explain the intended application and is not imported.
