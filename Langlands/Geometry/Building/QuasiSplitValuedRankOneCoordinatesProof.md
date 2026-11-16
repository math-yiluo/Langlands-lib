# Existence of coherent valued rank-one coordinates

Module `Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesProof`.
Workers 312 and 292, for Task 6651.

The theorem `Langlands.Geometry.Building.quasiSplitValuedRankOneCoordinates`
proves exactly `QuasiSplitValuedRankOneCoordinatesStatement.{u}`, at an arbitrary
universe `u`. Its inputs are a nonarchimedean local field `F` of any
characteristic, an affine group scheme `H` over `K = UnramifiedClosure F`,
supplied building data `B`, a proof that the whole centralizer of its maximal
split torus is a torus, and an indivisible relative root `b`. For each such
root it gives valued SL2 coordinates if `2 • b` is not a relative root, and
valued SU3 coordinates if `2 • b` is a relative root.

The proof applies the published theorem
`algebraicRankOneCoordinatesExistence` from
`AlgebraicRankOneCoordinatesExistenceProof` over `K`, to `H`, the maximal split
torus `B.S`, and the commutative torus `B.centralizerTorus hZ`. The required
connected reductivity, maximality, whole-centralizer representation and
factorization of the split torus inclusion are respectively
`B.isConnectedReductive`, `B.isMaximalSplitTorus`,
`B.centralizer.isRepresentedBy` and `B.centralizer.comp_eq`. This produces both
algebraic coordinate alternatives together with membership of the image of the
standard Weyl element in `normalizerPoints B.i`.

In the nonmultipliable branch the proof passes that algebraic record, its Weyl
normalization, and the root membership `hb.1` to
`ValuedSL2RootCoordinates.ofAlgebraic`. In the multipliable branch it passes
the corresponding data and the double-root hypothesis to
`ValuedSU3RootCoordinates.ofAlgebraic`. Both constructors are published in
`ValuedRankOneCoordinateSpecialization`. The SU3 Weyl point used there is
definitionally the point in the algebraic existence theorem.

These constructors preserve the common field or quadratic tower, the positive
and negative coordinate equivalences and full-centralizer characters, the
single rank-one homomorphism, and the actual induced-torus coroot morphism.
They supply a common origin in the given apartment and the two SL2 or four
SU3 depth identities. As described in the constructors' paired Markdown,
the origin and depth comparisons come from
`ValuedRankOneCoordinateAssembly` and `ValuedSU3CoordinateAssembly`;
`IntegerValuation.isNormCalibrated_henselianSeparableAddValuation` supplies norm
calibration and `SU3Root.henselianSeparableAddValuation_quadratic_bar` supplies
quadratic-conjugation invariance. All valuations remain normalized on `K`,
including the SU3 `towerDepth` and `towerCentralDepth` formulas.

This proof is an internal composition of those Library theorems and
constructors. It adds no premises or characteristic restriction, assumes no
coordinate-existence, apartment-comparison or consumer proposition, and makes
no change to the target statement or its imported records. The source
provenance of the target and algebraic and valuation constructions is
documented in their paired Markdown; this module cites no additional source.
