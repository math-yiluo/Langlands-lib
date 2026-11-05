# Actual normalizer equivariance of derived root-function pullback

This internal derivation combines the actual normalizer map with normalized
root-function pullback through a supplied derived inclusion.

First, in any central-complement torus diagram from
`CentralComplementNormalizer`, assume both acting maps are monic. The
normalizer map is the original rational-point map restricted to the actual
normalizer groups. Its torus automorphism square gives character Weyl-action
compatibility by applying inverse automorphisms. Tensor induction also
proves compatibility of the original real cocharacter maps and actions.

When the target group is locally of finite type and `a` is an actual
ambient root, `realizesReflection_centralComplementNormalizerMap` sends a
source reflection along `e ≫ a` to a target reflection along `a`. For the
character flip, centrality makes both the root and its Weyl transform vanish
on the central factor. Product character detection therefore reflects
equality from their restrictions to the retained torus. For fixation of
the entire ambient root hyperplane, product spanning decomposes every real
cocharacter into retained and central contributions. The source reflection
fixes the retained contribution when the root evaluates to zero; the
ambient normalizer fixes the central contribution by centrality. No
surjectivity of the retained torus map alone is used.

Now supply the derived diagram and assumptions of `DerivedFunctions`:
affine `D` locally of finite type, affine smooth `G`, an actual derived
inclusion `d`, the commuting square, split tori, and the flat-surjective
central-complement product with central ambient image. Additionally assume
the ambient acting torus is maximal split and the two acting maps are monic.

`derivedTranslationEquiv_translationAction` proves that the constructed
reduced translation equivalence intertwines the two original normalizer
derivatives, by induction on quotient representatives.
`RootFunctionFamily.derivedNormalizedPullback` regards the previously
constructed pullback as a map between the actual normalized-family subtypes;
its injectivity follows from the normalized-family comparison.
`RootFunctionFamily.derivedPullback_smul` proves equivariance of the full
normalized-family pullback. For actual roots and root-group points, reindex
by the proved root bijection, apply Weyl compatibility and actual
root-subgroup conjugation, then use the literal rational-point
homomorphism. Off the actual roots or root groups, normalization gives
infinity on both sides.

Finally, `equipollent_smul_derivedPullback_iff` detects preservation of a
normalized ambient family's equipollence class after pullback. It combines
the preceding equivariance with the proved equipollence comparison.

All conclusions follow from the imported actual maps, root groups,
central product comparison and normalized-family definitions. Structural
data remain supplied. This module does not assert valuation axioms or
construct the source apartment or the final normalizer-action equality.
