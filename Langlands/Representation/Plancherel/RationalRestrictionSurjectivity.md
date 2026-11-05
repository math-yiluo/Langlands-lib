# Actual valuation-image maps and unitary character extension

This is a derived construction toward Waldspurger, *La formule de Plancherel
pour les groupes p-adiques*, I.1, printed p.239 (PDF p.5). That passage defines
the common norm kernel, the unramified characters and their unitary subgroup,
and states that restriction from the unitary unramified characters of \(G\) to
those of its split component is surjective with finite kernel. It then fixes
the character measures using this restriction.

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.6, printed p.108 (PDF p.114), proves equality of the split-component norm
kernel with the inverse image of the group norm kernel. His argument uses
finite index of algebraic-character restriction and the absence of torsion in
positive norms. The present construction uses integer valuations and the
published finite-index theorem to prove injectivity of the actual image map.
It extends circle-valued characters along that map by the divisibility of the
circle group. This is an internal proof route for the surjectivity assertion,
rather than a new structural hypothesis.

## Actual objects and hypotheses

The field \(F\) is any nonarchimedean local field with the project's
`IsNonarchimedeanLocalField` structure, in an arbitrary universe. There is no
characteristic-zero or split-group restriction. The algebraic objects are the
shared `GroupScheme` and `CommGroupScheme` objects.

`rationalDiscreteValuationImage G` is the existing discrete copy of the actual
image of `rationalCharacterValuation G` in the integer dual of all rational
algebraic characters. Its projection is the existing
`rationalValuationImageProjection G`; it is surjective by construction.

The valuation-image declarations and the general circle-character extension
need no rational-point topology, affineness
or finite-generation premise. The final two declarations assume the underlying
schemes of the source and target groups are affine and locally of finite type.
Their rational-point groups have the canonical `rationalPointTopology`. The
unitary unramified character groups and their compact-open topologies are the
existing ones, compared with the circle-valued dual of the actual image by
`rationalCanonicalUnitaryImageUnramifiedContinuousEquiv`.

## The actual image map

For a group-scheme morphism \(f:H\to G\), `rationalValuationImageMap f` is a
multiplicative homomorphism from the actual discrete valuation image of \(H\)
to that of \(G\). It is constructed by the actual rational-point map on the
quotients by their common norm kernels, followed by the published quotient-to-
image equivalences. The previously proved
`rationalCommonNormKernel_le_comap` supplies the inclusion needed for this
quotient map.

`rationalValuationImageMap_projection` proves that the new map takes the
valuation of a point \(h\) to the valuation of \(f(h)\). Consequently,
`rationalValuationImageMap_apply` identifies its integer coordinate at a
character \(\chi\) with the source coordinate at the actual restricted
algebraic character `GroupScheme.characterRestrict f chi`.

`rationalValuationImageMap_injective_of_finiteIndex` assumes finite index only
of the range of this **algebraic-character restriction**. To detect equality
of two source integer valuations at any source character, the proof chooses
a positive multiple lying in that range. Equality after the image map gives
equality on this multiple, and multiplication by a positive integer is
injective on \(\mathbb Z\).

For an actual split component \(s:T\to G\) of a connected reductive group,
`rationalValuationImageMap_injective` discharges that premise using the
published theorem
`GroupScheme.IsSplitComponent.finiteIndex_range_characterRestrict`.
Its inputs are `GroupScheme.IsConnectedReductive G` and
`GroupScheme.IsSplitComponent s`. It does not assume finite index of the
actual split-component valuation image in the group's valuation image.

## Unitary character extension and restriction

`rationalUnitaryUnramifiedCharacterRestrict_surjective_of_injective` proves
surjectivity of the existing continuous restriction map for any morphism
whose actual image map is injective. Given a target unitary unramified
character, the proof first transports it to a circle-valued character of the
source's discrete image.

The public `exists_circle_character_extension` lemma uses the surjective additive exponential
`Circle.expHom` from \(\mathbb R\) to `Additive Circle`. Divisibility of
\(\mathbb R\) implies divisibility of `Additive Circle`. Mathlib's
`Module.Baer.of_divisible` and
`Module.Baer.extension_property_addMonoidHom` then extend the given character
along the injective actual image map. This extension property allows
independent group universes. The resulting character of the target actual
image is continuous because that image is discrete.

Finally the proof transports the extension back to a continuous unitary
unramified character on the actual rational-point group. The projection law
for `rationalValuationImageMap` and the extension equation prove that its
restriction is the original character, point by point.

`rationalUnitaryUnramifiedCharacterRestrict_surjective` specializes this
construction to an actual split component of a connected reductive group.
The split-component and reductivity assumptions discharge the injectivity
premise by the preceding theorem. Surjectivity is a conclusion; no character-
extension or desired restriction-surjectivity premise is inserted.

## Scope

This pair supplies the actual map and its intrinsic coordinate and extension
laws. It closes the displayed surjectivity obligation under the stated actual
scheme and local-field hypotheses. It does not prove finite index of the
actual valuation image, finiteness of the restriction kernel, or the source's
Haar normalization. The published conditional restriction-kernel results
still retain the actual-image finite-index premise. The separate rank
comparisons, general real-part descent, complex periods, coefficient spaces,
wave packets, spectral finiteness, inversion and Plancherel remain outside
this construction.
