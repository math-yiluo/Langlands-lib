# Chamber complement lemmas for the Iwahori–Weyl quotient

This derived internal unit supplies the chamber-complement step for the
existing Iwahori–Weyl targets. Its proposition
`IwahoriWeylChamberReductionStatement` quantifies over the same arbitrary-universe
local fields, group schemes and actual data `P` as the published targets. It
asserts that the apartment axioms, the actual exact-sequence conclusion, and
unique affine-Weyl transport between every two given chambers imply the actual
chamber-splitting conclusion for every chamber. The theorem
`iwahoriWeylChamberReduction` implements this conditional reduction.

The exact sequence and unique transport are explicit intermediate premises.
This unit does not prove `IwahoriWeylExactSequenceStatement` or
`IwahoriWeylChamberSplittingStatement`, nor does it discharge the generic
affine-chamber transitivity theorem. Their final hypotheses remain unchanged.
In particular, the full `P.chamberStabilizer C` and full component quotient
`G(F)/G(F)^0` are retained.

The general lemma `IwahoriWeylAlgebra.image_isComplement_stabilizer` concerns a
surjective homomorphism `f : A →* B`, an action of `A` on `X`, a subgroup `H`,
and a point `x`. It assumes that the kernel fixes `x`, that elements of `H`
fixing `x` have trivial image, and that `H` can take every point in the ambient
orbit back to `x`. It concludes that the images of `H` and the full stabilizer
of `x` are complementary in `B`, in that order. For disjointness,
representatives of an element in both images differ by a kernel element, so
the `H` representative fixes `x` and has trivial image. For the product
decomposition, choose `h` taking `a • x` back to `x`; then
`a = h⁻¹ * (h * a)` with `h * a` in the full stabilizer.

For a real affine torsor, `AffineRootSystem.image_facet` shows that an affine
automorphism preserving the root set maps the facet of `x` onto the facet of
its image. This is exactly the existing `facetRel_apply_iff` in both directions.
`AffineRootSystem.IsChamber.image` additionally transports the nonvanishing of
all roots at a chamber representative, using invariance of the root set under
composition. These facts require neither an affine-root-system axiom nor
positive rank. For the actual data `P`, the image of a subset under
`P.apartment.normalizerAffineEquiv n` is definitionally `n • C`.
The apartment axiom giving membership in the extended affine Weyl group
therefore proves `normalizer_smul_isChamber`.

The actual-data lemma `affinePart_isComplement_chamberStabilizer_of_action`
assumes normality of `P.normalizerZero` and an isomorphism from `P.affinePart`
to the existing affine Weyl group, with its value on every representative
equal to the existing normalizer action. It also assumes that affine Weyl
elements fixing `C` are the identity and that each normalizer translate of
`C` can be taken back to `C` by an affine Weyl element. Apply the general
image-complement lemma to the actual quotient projection from the normalizer
and the subgroup `P.normalizerZeroComponent`. A kernel element has trivial
image in the affine part, hence acts as the identity by the representative
formula. Freeness transfers through injectivity of the isomorphism.
Transitivity transfers through its surjectivity and the surjectivity of
`P.affinePartMk`. The two images are exactly the published `P.affinePart`
and full `P.chamberStabilizer C`.

Finally, `iwahoriWeylChamberSplitting_of_unique_chamber_transport` extracts the
two normalities, action-compatible isomorphism and component surjectivity from
the actual exact sequence. Unique transport from `C` to itself supplies
freeness by comparison with the identity. Unique transport from `n • C` to
`C`, together with normalizer preservation of chambers, supplies transitivity.
The quotient helpers then give normality of the affine part and bijectivity
of the component homomorphism restricted to the full chamber stabilizer.
This proves every clause of the local splitting conclusion under the stated
intermediate premises.

The provenance is internal: group-action and quotient algebra applied to the
existing definitions, plus root-relation invariance already proved in
`AffineRootSystem`. No new geometric assertion is assumed implicitly and no
new source theorem is claimed as proved here. The contextual source for the
consumer remains the source-backed `IwahoriWeylStatement` pair.
