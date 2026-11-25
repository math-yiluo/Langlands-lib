# Hermitian models for rank-one outer type-A indices

`Langlands.GroupScheme.outerTypeARankOneHermitian` proves the exact published
`Langlands.GroupScheme.OuterTypeARankOneHermitianStatement.{u}` at every
universe `u`, with no additional premise.

The proof applies the published theorem
`outerTypeARankOneHermitian_of_presentation_and_splitRank` to the two
published unconditional proofs `outerTypeAHermitianPresentation` and
`hermitianMatrixSplitRank`, all at the same universe. Their modules are,
respectively,
`Langlands.GroupScheme.SimplyConnected.OuterTypeARankOneHermitianReduction`,
`Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationProof`
and `Langlands.GroupScheme.Rational.HermitianMatrixSplitRankProof`.

The presentation proof constructs a separable quadratic extension and an
invertible Hermitian Gram matrix from the actual outer type-A index. It
also constructs injective matrix homomorphisms on every relative test
scheme, with exactly the determinant-one Hermitian isometries as image
and with the required naturality. The split-rank proof identifies the
actual split rank with the attained maximal dimension of a totally
isotropic subspace for this full pairing.

The reduction uses the hypothesis `splitRank G = 1` to obtain an attained
isotropic line and the dimension bound on every totally isotropic
subspace. Its coordinate and presentation constructions then give an
anisotropic diagonal middle on `Fin (n - 1)`, units witnessing the
diagonal weights, and an actual group-scheme isomorphism
`G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw`.
These are exactly the data required by the target existential.

All original hypotheses on the field, affine locally finite type group
scheme, simply connected and absolutely almost-simple structure, actual
Tits index and split rank are retained. Both fields lie in the arbitrary
common universe `u`. Every characteristic, including characteristic two,
is covered. The isomorphism uses the natural matrix presentation on all
test schemes.

The provenance is composition of the three published internal results
named above. Their paired Markdown describes the underlying constructions
and source context. This proof uses no downstream local rank-one
classification or Kneser–Tits theorem.
