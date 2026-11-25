# Actual jet determinant lines from affine cotangent frames

This module constructs a tensor-power isomorphism for the existing
actual identity-jet determinant line. Let `G` be a smooth affine group
scheme over an arbitrary scheme `S`. Supply a cover of `S` by affine
opens and actual free sheaf frames of `G.cotangentAtIdentity` on those
opens, all indexed by one fixed finite type `σ`.

For specified augmentation-ideal lifts of each cotangent section basis,
`adaptedCoverFrames` is the family of actual adapted jet frames on this
cover. The theorem `adaptedCoverFrames_cocycle` identifies its determinant
cocycle with the cotangent determinant cocycle raised to
`jetExponent σ n`, by the actual overlap transition formula. Equality
of determinant values also gives equality of the corresponding units.
The proof accounts for the harmless choices of decidable equality used
by the two matrix determinant presentations.

The definition `determinantPowerIsoOfAffineFrames` then gives an actual
module-sheaf isomorphism

`(IdentityJet.determinant G n).obj ≅
  tensorPow
    (finiteLocallyFreeDeterminant
      (G.cotangentAtIdentity_hasFiniteLocalBasis hG)).obj
    (jetExponent σ n)`.

Both determinant lines here are the existing chosen actual determinant
constructions. The proof compares each with its supplied fixed-index
frame presentation using `finiteDeterminantPresentationIso`, identifies
the two cocycles by the transition calculation, and applies the actual
cocycle tensor-power isomorphism. This includes jet order zero.
`chosenDeterminantPowerIsoOfAffineFrames` chooses augmentation-ideal
lifts using cotangent quotient surjectivity, so it requires only the
affine cotangent frame cover.

The provenance is internal: the isomorphism is assembled from the
actual sheaf frames, their determinant transitions, and the two generic
presentation comparisons in this module. The fixed-index affine cover is
a retained hypothesis. Variable global rank, comparison with the
actual Lie determinant dual, stabilizing base-line factors and
geometric ampleness are separate obligations toward
`FiniteAffineParabolicDeterminantDualAmpleStatement`, the statement this module
serves, which `Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantDualAmpleProof`
proves. This module proves no ampleness theorem.
