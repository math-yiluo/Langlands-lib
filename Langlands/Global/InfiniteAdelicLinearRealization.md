# A closed linear realization of the archimedean points of a reductive group

`Langlands.Global.InfiniteAdelicLinearRealization`. For a number field `F` and a connected reductive
group scheme `G` over `F`, the archimedean points `G(F_∞) = InfiniteAdelicGroupPoints F G`, with the
Library's manifold structure, have a closed linear realization in the sense of
`Langlands.LinearLieGroup.IsClosedLinearRealization`. Namespace
`Langlands.Global.InfiniteAdelicGroupPoints`.

## Statements

- `matrixRealization F G ρ : InfiniteAdelicGroupPoints F G →* (ArchimedeanMatrix F N)ˣ`, for a matrix
  representation `ρ : MatrixRepresentation G (Fin N)`: the matrices of `ρ` on points over
  `InfiniteAdeleRing F`, read in mixed coordinates by `archimedeanGLCoordinates F N`.
  `matrixRealization_eq` identifies it, by definition, with `GeneralLinear.coefficientCoordinates` of
  `x ≫ ρ.hom.hom` for the coefficient map `InfiniteAdeleRing.ringEquiv_mixedSpace F`.
- `isClosedLinearRealization_matrixRealization`: for `hG : IsConnectedReductive G` and a closed
  representation (`IsClosedSubgroup ρ`), `matrixRealization F G ρ` is a closed linear realization for
  the atlas `reductiveChartedSpace F G hG` with model `smoothModel F hG.smoothDimension` (and the
  completion scalars `completionRCLike F v`).
- `exists_isClosedLinearRealization`: some `N` and some
  `ρ : InfiniteAdelicGroupPoints F G →* (ArchimedeanMatrix F N)ˣ` form a closed linear realization.
  The representation is `InfinitePlaceGroupPoints.exists_closedMatrixRealization`.

## Proof of the three conditions

- *Closed embedding*: `MatrixRepresentation.isClosedEmbedding_affineMatrix` for the coefficient ring
  `InfiniteAdeleRing F`, followed by the homeomorphism `archimedeanGLCoordinates F N`.
- *Smoothness*: the identity of `G(F_∞)` is smooth, hence coordinate smooth for the mixed
  coefficient map (`reductive_contMDiff_iff_coordinateSmooth`); composing with `ρ` keeps coordinate
  smoothness (`CoordinateSmooth.postcomp`), and for `GL_N` coordinate smoothness is smoothness into
  the units of the matrix algebra (`GeneralLinear.coordinateSmooth_iff_contMDiff`).
- *Testing smoothness through `ρ`*: if `x ↦ ρ (p x)` is smooth into the matrix algebra, it is smooth
  into the units (`LinearLieGroup.contMDiff_units_of_contDiff_val`), hence coordinate smooth for
  `GL_N`; a closed representation reflects coordinate smoothness
  (`MatrixRepresentation.coordinateSmooth_of_postcomp`), and coordinate smoothness of `p` is
  smoothness for the reductive atlas.

This is the global version of the place-by-place criterion `contMDiff_iff_realizationMatrix` of
`Langlands/Global/InfinitePlaceRealizationSmooth`. With it the Dixmier–Malliavin theorem
(`Langlands/Representation/Archimedean/DixmierMalliavin`) applies to `G(F_∞)`.

`isClosedLinearRealization_matrixRealization_of_smooth` uses the atlas of the supplied smooth relative dimension. The mixed regular-coordinate criterion proves both smoothness clauses, and the reductive version specializes this result to the canonical dimension.
