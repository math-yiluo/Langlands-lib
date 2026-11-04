# Actual unramified characters in intertwining threshold regions

This internal construction realizes the existing actual-root threshold regions
by actual valuation-image characters and by the existing continuous unramified
characters in the canonical rational-point topology. The field is an arbitrary
nonarchimedean local field in the shared interface, in any universe and
characteristic. It uses the shared group schemes, full character spaces and
actual valuation images.

`exists_positiveImageCharacter_mem_intertwiningRegion_of_injective` assumes
actual splitness of `A`, a morphism `j : A.toGrp ⟶ M` whose actual valuation-image
map is injective, an actual morphism `i : A.toGrp ⟶ G` with affine `G`, a supplied
bilinear form, two supplied subgroup functors and a real threshold. From a
point in the real threshold region, the proved positive-character extension
theorem supplies a real functional on the actual image of `M`. Its positive
image character restricts exactly to the split-torus positive character of
the original parameter. The proved normalized-real-part formula therefore
puts this character in the required image-character region. In particular,
the witness is positive on the entire actual image.

`imageCharacterIntertwiningRegion_nonempty_iff_of_injective` also proves the
converse: applying the normalized real part of restriction to any character
witness gives a real witness. Neither this equivalence nor the positive-witness
theorem requires a nondegenerate form, finiteness of the indexing set, smoothness
of `G`, or an identification of the two subgroup functors with radicals. The
specialization `imageCharacterIntertwiningRegion_nonempty_iff` assumes
`IsConnectedReductive M` and the actual predicate `IsSplitComponent j`. The
existing actual-image injectivity theorem discharges injectivity.

For smooth affine `G`, a nondegenerate supplied form and any integral
cocharacters `nu` and `eta`, the dynamic subgroup region is nonempty for every
real threshold. The proof combines the existing real-region nonemptiness
theorem with positive-character extension.
`exists_positiveImageCharacter_mem_intertwiningRegion_dynamic` retains a witness
of the form `rationalImagePositiveCharacter M psi`;
`imageCharacterIntertwiningRegion_dynamic_nonempty` and
`characterIntertwiningRegion_dynamic_nonempty` give the corresponding set
nonemptiness statements on image characters and ordinary point characters.
The indexing set is unchanged: all actual relative roots with positive
`nu`-pairing and negative `eta`-pairing remain present, including multipliable
roots. These are the dynamic groups of `nu` and `-eta`; no unspecified common
Levi or opposite-radical identification is inferred.

In the canonical-topology section, `M` is explicitly affine and locally of
finite type. `canonicalUnramifiedIntertwiningRegion` is a subset of the
existing `unramifiedCharacters` group for the actual rational norm characters
of `M`. Its domain uses exactly `rationalPointTopology F M.X`. Membership
means that the underlying point character lies in the existing
`characterIntertwiningRegion`. Thus these characters are continuous and
trivial on the actual common norm kernel by their existing type; no new
character group or topology is introduced.

The published `rationalCanonicalImageUnramifiedContinuousEquiv` has the actual
image-character pullback as its forward evaluation formula. Consequently its
image belongs to the canonical unramified region exactly when the original
image character belongs to the image-character region. Surjectivity of the
same equivalence proves
`canonicalUnramifiedIntertwiningRegion_nonempty_iff_image`, with no reductivity
or split-component hypothesis needed for this comparison.
`canonicalUnramifiedIntertwiningRegion_nonempty_iff` adds the actual
split-component hypotheses to compare with the real region, and
`canonicalUnramifiedIntertwiningRegion_dynamic_nonempty` specializes to the
nondegenerate dynamic case.

The provenance is internal: the implemented proofs compose the actual
positive-character extension, its normalized-real-part identity, the proved
dynamic real-region nonemptiness, and the existing canonical continuous
image/unramified equivalence. No real-part surjectivity, character realization
or nonemptiness conclusion is assumed as structural input. Central directions,
empty indexing sets and rank zero are retained. The form remains explicit;
one may instantiate it with a constructed nondegenerate ambient-induced form,
but no comparison with an independently selected metric is asserted here.
These results supply character realization for the prospective strict
threshold regions used in the Plancherel program. They do not prove that a
specified pair of parabolics has these dynamic radicals, identify a common
Levi, or prove finite length, intertwining convergence, rational continuation
or a Plancherel theorem.
