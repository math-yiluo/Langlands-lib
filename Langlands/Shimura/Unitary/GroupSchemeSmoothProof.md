# Smoothness of the actual rational Harris group

Authors: Worker 57 (product, splitting and descent proofs); Worker 522
(scalar normalization proof, documentation and verification).

`Langlands.Shimura.CentralSimpleUnitaryData.rationalGroupSchemeSmooth` proves
the exact proposition `RationalGroupSchemeSmooth D` from
`Langlands.Shimura.Unitary.GroupSchemeSmoothStatement`. For every embedding
family `Φ` and every `HarrisSignatureCharts D.toSecondKindInvolution n Φ`,
the structure morphism `D.rationalGroupScheme.X.hom` is smooth in Mathlib's
scheme-morphism sense, including local finite presentation.

The proof retains the published target's small-type number fields `E` and `K`,
total reality and total complexity, quadratic extension, actual central-simple
algebra `A` with its second-kind involution, and compatible rational scalar
towers. It quantifies over all supplied chart families. It assumes neither
chart existence nor smoothness of a scheme.

`GeneralLinearProduct.smooth_groupScheme` first proves smoothness of the
actual split product. It applies the imported
`GeneralLinear.smoothStatement` to each `Fin n` matrix factor, then uses
`GroupScheme.smooth_pi`, `smooth_gm` and `smooth_tensor`. This auxiliary
result allows every natural rank and every finite small index type.

`complexRationalGroupScheme_smooth` forgets the group laws in the published
`D.complexGroupSchemeIso C`, obtaining an isomorphism in `Over Spec(ℂ)`.
The helper `smooth_of_over_iso` transfers smoothness of the split product to
the actual iterated complex pullback of the rational Harris scheme.
In the private theorem `rationalGroupSchemeSmooth_of_tower`, the inverse of
`D.complexDirectGroupSchemeIso`
transfers this result to the direct rational base change along
`rationalComplexBaseMap : Spec(ℂ) ⟶ Spec(ℚ)`.

`rationalComplexBaseMap_fpqc` proves that this actual scalar map is
surjective, flat and quasi-compact. The coefficient field extension `ℂ/ℚ`
is faithfully flat; `flat_and_surjective_SpecMap_iff` gives the first two
scheme properties, and affineness gives quasi-compactness. Mathlib's
`LocalFlatDescent` instance for smoothness, applied through
`MorphismProperty.of_pullback_snd_of_descendsAlong`, therefore proves
smoothness of the original rational structure morphism.

The published target does not require `IsScalarTower E K A`. The preceding
complex-splitting argument uses that compatibility, so the final theorem
constructs it internally. Centrality of `A` over `K` puts each given
`E`-scalar in the image of `algebraMap K A`. Simplicity makes `A` nontrivial,
so this map from the field `K` is injective. Choosing the scalar preimages
therefore gives a ring homomorphism `e : E →+* K`, with the same composite
map `E → A` as the original `E`-algebra structure on `A`. The new `E`-algebra
structure on `K` satisfies the required tower.

The original extension degree gives
`finrank ℚ K = finrank ℚ E * 2`. The tower dimension formula for the new
embedding, followed by cancellation of the positive rational dimension of
`E`, shows that the new extension is again quadratic. The theorem then
rebuilds the central-simple unitary datum using the same involution and
central-simple algebra fields. The underlying CM conjugation is unchanged:
both definitions use the absolute CM conjugation of `K`, and their
proof-valued instance arguments are irrelevant. The chart data transfer
unchanged because they use the same `E`-algebra structure on `A`, involution,
`K`-scalar map to `A`, and embedding family `Φ`. The private tower theorem
now applies. Its rational scheme is definitionally the original one,
including its rational basis and restricted involution. Thus this
normalization adds no assumption, changes no chart family, and proves
smoothness of the given rational scheme.

This is an internal geometric consequence of the published rational model,
complex splitting and base-change comparison, using Mathlib's smoothness
and descent APIs. The separately proved general linear result is imported
from `Langlands.GroupScheme.GeneralLinearSmoothProof`. The conclusion does
not supply reductivity, Shimura moduli, a canonical model, a reflex field
identification or geometric level schemes.
