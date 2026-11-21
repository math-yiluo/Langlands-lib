# Smoothness into an infinite-place point group through a closed representation

Module `Langlands.Global.InfinitePlaceRealizationSmooth`. Internal supporting result: for the
published atlas on `G(F_v)` (an archimedean completion `F_v` of a number field `F`), smoothness of a
family of points is detected by the matrix entries of any closed matrix representation of the base
change `G_v` of `G` to `F_v`.

## Declarations

- `MatrixRepresentation.coordinateSmooth_of_postcomp` (namespace
  `Langlands.GroupScheme.MatrixRepresentation`): for a closed representation
  `ρ : MatrixRepresentation G n` over a field `k`, a parameter family `p` of `A`-points of `G` is
  coordinate-smooth (every global regular function has a smooth value after the coefficient map
  `c : A →+* B`) as soon as the family `x ↦ p x ≫ ρ` of general linear points is.
  *Proof.* `ρ` is surjective on global sections (closed immersion of affine schemes,
  `IsClosedImmersion.isAffine_surjective_of_isAffine`), so every regular function of `G` is the
  pullback of one of `GL_n`, and evaluation commutes with pullback
  (`affinePointEvaluation_postcomp`).
- `InfinitePlaceGroupPoints.realizationMatrix F G v ρ : G(F_v) →* GL (Fin N) F_v` for
  `ρ : MatrixRepresentation G_v (Fin N)`, where `G_v = completionBaseChange F G v`: the published
  base-change comparison `affinePointsBaseChangeMulEquiv F F_v F_v G` followed by
  `ρ.affineMatrix`.
- `InfinitePlaceGroupPoints.contMDiff_iff_realizationMatrix`: for `hsmooth` (smoothness of
  relative dimension `d`), a closed `ρ`, and any `p : M → G(F_v)` from a charted space with model
  `I`, `p` is `C^∞` for `InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth` if and only if
  every entry `x ↦ (realizationMatrix F G v ρ (p x)).val i j` is `C^∞`.
  *Proof.* The published criterion `InfinitePlaceGroupPoints.contMDiff_iff_coordinateSmooth`
  turns smoothness into coordinate smoothness of `G`; `coordinateSmooth_baseChange_iff` moves it to
  `G_v`. Forward: postcompose with `ρ` (`CoordinateSmooth.postcomp`) and apply the general linear
  criterion `GeneralLinear.coordinateSmooth_iff_contMDiff`; the entries are continuous linear
  functions of the matrix. Backward: assemble the entries into a smooth map to the matrices, use
  the general linear criterion (with `Units.isOpenEmbedding_val`), and reflect coordinate smoothness
  through `ρ` with `coordinateSmooth_of_postcomp`.
