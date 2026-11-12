# Properties after composition of bases

Author: Worker 109.

This internal module derives morphism and atlas transport from the actual
`BaseCompositionGeometry` construction. It does not claim any external
literature theorem as proved. All schemes and test schemes retain the arbitrary
universe `u`, with presheaves valued in `Type (u+1)`.

For every morphism `g : S ⟶ T`, `pullbackIso` identifies the composition of
the actual presheaf pullback with the pullback of the composed natural
transformations. It is the isomorphism supplied by the already proved
`map_isPullback`; `pullbackIso_hom_fst` and `pullbackIso_hom_snd` identify both
projections. The mapped relative diagonal becomes the new relative diagonal
under this comparison, since its composites with both projections are
identities. Thus `relative_pullback_diagonal` transports every represented
scheme-morphism property of a relative diagonal that respects isomorphisms.
In particular `separated_spaceMap` preserves separatedness of morphisms of
spaces for arbitrary `g`.

`fromScheme_square` proves that composing both charts in a commuting scheme
square gives a commuting square over `T`. It uses functoriality of the
presheaf construction and naturality of `schemeIso`. Consequently,
`locallyOfFiniteType_spaceMap` and `smooth_spaceMap` retain the original
chart squares witnessing those morphism properties. The new charts are
etale, the source chart remains surjective, and the underlying scheme map is
unchanged. There is no representability assumption on the space morphism.
`morphismChart` constructs the composed actual `EtaleMorphismChart`;
`morphismChart_sourceSurjective` transports its separate source-surjectivity
condition, and `morphismChart_smoothOfRelativeDimension` retains any supplied
smooth relative dimension of the same scheme map.

Structural atlas properties have an additional hypothesis on `g`.
`hasAtlasProperty_space` assumes a scheme-morphism property `P` stable under
composition, an original atlas with `P` on its structure map, and `P g`.
The same source scheme over `T` is an etale surjective atlas and its
structure map is the original structure map followed by `g`, so it has `P`.
No isomorphism invariance assumption on this structural `P` is needed.

For affine bases, `finiteTypeOverRing_space` specializes this construction
to the arithmetic interface `FiniteTypeOverRing`. It assumes both
`LocallyOfFiniteType g` and `QuasiCompact g`. The original atlas is locally
of finite type and quasi-compact over its base; composition of the two
structure maps retains both properties. This is the atlas-based
`FiniteTypeOverRing` from `AdelicSpaceLevelPointsStatement`, and does not
assert a comparison with the separate `FiniteTypeOverBase` interface.

Separatedness here is a property of the morphism between the two composed
spaces. The module does not assert separatedness of a space over `T` for
arbitrary `g`. It also does not yet transport general point-surjectivity,
geometrically connected fibres, or quasi-compactness of a nonrepresentable
morphism. Those and the arithmetic and topological inputs remain obligations
for the unchanged unconditional adelic smooth-openness target.
