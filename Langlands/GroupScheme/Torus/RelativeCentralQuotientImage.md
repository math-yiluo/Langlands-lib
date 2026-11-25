# Maximal torus images in relative central quotients

`Langlands.GroupScheme.RelativeCentralQuotientImageReductionStatement.{u}` is the named `Prop`-valued statement recording
the full forward relative maximal-torus construction with the same explicit quotient-existence, reductivity and multiplicative-type-kernel hypotheses.
`Langlands.GroupScheme.relativeCentralQuotientImageReduction` proves this proposition by the existing helper theorem.
The helper signatures and all mathematical hypotheses are retained; the
other results below are proved companion helpers.

This internal assembly result constructs the forward maximal-torus image
for a supplied central quotient of reductive group schemes over every
scheme. It explicitly assumes
`RelativeCentralMultiplicativeTypeQuotientStatement`, which provides affine
quotients by central multiplicative-type subgroups. The given closed
central kernel is also assumed to be of multiplicative type, and both
ambient groups are assumed reductive.

The result returns an actual target relative torus and closed inclusion,
maximal on every residue fibre, together with an fppf map from the given
source torus. The ambient square commutes, and the full inverse image of
the target torus range is exactly the source torus range on all test
schemes. No finiteness or smoothness of the central kernel is required.

The proof uses self-centralization of relative maximal tori to factor the
central kernel through the source torus. This factor is closed, and its
centrality follows from commutativity of the torus. The assumed quotient
construction supplies its affine quotient. The published quotient-subgroup
embedding construction then descends the source inclusion to a closed
inclusion into the ambient quotient. Equality of the actual kernel
functors and containment of the ambient kernel in the source torus give
the full inverse-image identity. The affine fppf image of a relative torus
is a relative torus. Finally,
`IsFibrewiseMaximalTorus.image_of_centralFppfHom` proves residue-fibre
maximality of this supplied image.

This derives the forward torus construction used in
`RelativeCentralQuotientStatement` from the named quotient-construction
input and the published structural results. It does not prove that input,
show that every flat central closed subgroup is of multiplicative type,
or prove the reverse torus construction or target reductivity.
