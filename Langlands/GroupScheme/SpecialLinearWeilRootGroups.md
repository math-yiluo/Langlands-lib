# Actual coordinate-root maps and generation for Weil-restricted split SLₙ

For fields `F`, `E : Type u` with an algebra structure and
`FiniteDimensional F E`, and any finite index type `n : Type` with a
decidable equality, `SpecialLinear.WeilRoot.groupScheme F E` is the
existing actual affine Weil restriction of the existing split SLₙ scheme
over `E`. The definition `additiveScheme F E` is the actual restriction
of the additive group over `E`. These constructions impose no local-field,
separability, Galois or characteristic restriction.

The instance `SpecialLinear.locallyOfFiniteType_groupScheme` proves that
the actual SLₙ scheme over any commutative base ring is locally of finite
type. Its coordinate ring is the quotient of the polynomial ring in the
finitely many matrix entries by the determinant-one relation; the existing
finite-type instances and spectrum criterion prove the result.
The additive scheme is affine and locally of finite type by its polynomial
coordinate description. These are proved prerequisites for the existing
Weil-restriction construction.

For any distinct indices `i`, `j`,
`rootMap F E hij : additiveScheme F E ⟶ groupScheme F E` is the actual
restricted morphism `AffineWeil.map` applied to the actual coordinate-root
map over `E`. Its source is the restriction of `Ga/E`; the construction does
not replace that source by a one-dimensional additive group over `F`.

The companion `Rational/AffineWeilPoints` constructs the natural
multiplicative comparison from rational points of an actual restricted
group to the original group over `E`.
Composing it with `SpecialLinear.Root.rationalMatrixEquiv E` defines
`WeilRoot.rationalMatrixEquiv`, identifying actual `F`-points of the
restricted SLₙ scheme with determinant-one matrices over `E`.

The theorem `rationalMatrixEquiv_rootMap` applies the companion naturality
theorem to the actual root morphism. Its matrix is exactly the original
`E`-rational root matrix after the rational comparison for the restricted
additive source. The original scalar-root witnesses therefore give
`exists_rational_rootPoint`: every scalar transvection over `E` is the image
of an actual `F`-rational point of the restricted additive group.

The theorem `eq_top_of_root_images` takes any abstract subgroup of the
restricted scheme's actual `F`-point group containing the ranges of all
these actual root maps. Its inverse image under the rational matrix
equivalence contains every scalar transvection over `E`.
The proved field-level transvection generation in `SpecialLinearRootGroups`
makes this inverse image the whole matrix group. Thus the original subgroup
is the whole actual rational-point group. No normality premise is needed;
empty and singleton matrix index types are included.

The provenance is internal. All group schemes and maps are the existing
affine restrictions of the actual SLₙ and additive constructions; the new
point comparison composes existing canonical equivalences. The only
generation input is the proved scalar-transvection result over the field
`E`. This unit does not compare dynamic or parabolic-radical subgroups under
restriction, identify these coordinate-root maps with arbitrary relative-root
subgroup functors, classify general factors, or prove the unrestricted local
Kneser–Tits statement.
