# `G(F)^0 = G(F)^1` for KP building data of `GL_N`

Module `Langlands.Geometry.Building.DepthZero.GeneralLinear.ZeroSubgroup`, namespace
`Langlands.Geometry.Building.GeneralLinearParahoric`.

For a nonarchimedean local field `F` and building data `D : KPBuildingDatum` of
`G = GL_N` over `F` satisfying `D.SatisfiesGroupAxioms`, the zero subgroup `G(F)^0` of
Kaletha–Prasad Definition 2.6.23 (`D.base.zeroSubgroup`) contains the norm-one subgroup
`G(F)^1 = Plancherel.rationalCommonNormKernel G`, the points whose determinant has valuation
one. With `ZeroSubgroupDatum.zeroSubgroup_le_rationalCommonNormKernel` the two are equal
(KP 15.1.33 states `G(k)^0 = G(k)^1` for `GL(X)`).

## Declarations

- `toMatrixGL_map_diagTorus`: a rational point of the diagonal torus maps to the diagonal matrix
  of its coordinates (`splitTorus.affinePointsEquiv`).
- `rationalCharacterEval_determinantCharacter` and `valuation_det_eq_one`: the determinant
  character evaluates to the determinant of the matrix, so a point of `G(F)^1` has determinant
  of valuation one.
- `isRepresentedBy_torusCentralizer_diagTorus`: the diagonal torus represents its own
  centralizer (`maximalTorusCentralizer`, `GeneralLinear.isMaximalTorus_diagonalTorus`).
- For parahoric building data `P`, an isomorphism `σ` of its split torus with the diagonal
  split torus and an automorphism `f` of `GL_N` with `P.i ≫ f = σ ≫ diagTorus`, the transported
  data `P.basedTransport σ f h` have the diagonal torus as maximal split torus, and:
  - `isSplitTorus_centralizer`: their minimal Levi subgroup is a split torus;
  - `diagGL_mem_zeroSubgroup`: every invertible diagonal matrix with entries of valuation one
    lies in their `G(F)^0`;
  - `exists_transvectionGL_mem_zeroSubgroup`: under the apartment axioms, their `G(F)^0`
    contains a nontrivial transvection `1 + t E_{kl}` for each `k ≠ l`;
  - `rationalCommonNormKernel_le_zeroSubgroup_of_diagonal`: under the apartment axioms,
    `G(F)^1` lies in their `G(F)^0`.
- `rationalCommonNormKernel_le_zeroSubgroup`: **for `D` satisfying the one-group axioms,
  `G(F)^1 ≤ D.base.zeroSubgroup`.**

## Proofs

`diagGL_mem_zeroSubgroup`: the minimal Levi subgroup represents the centralizer of the diagonal
torus, so it is isomorphic to the diagonal split torus
(`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`) compatibly with the inclusions. A
diagonal matrix with unit entries is the image of a point of `𝔾_m^N(F)^1`
(`SplitTorusValuation.integralUnitKernel_eq_rationalCommonNormKernel`), whose image in the
minimal Levi subgroup lies in `Z(F)^1`, hence in `Z(F)^0`
(`map_rationalCommonNormKernel_le_zeroSubgroup`).

`exists_transvectionGL_mem_zeroSubgroup`: at any point of the apartment, the valuation of the
root datum takes a finite value on some point `u` of the root group of `e_k − e_l`
(`IsRootDatumValuation.exists_ne_top`), so `u ≠ 1` (`IsRootDatumValuation.eq_top_iff`). The
point `u` is a transvection (`exists_eq_transvectionGL_of_mem_rootGroupPoints`) and lies in
`G(F)^♮ ≤ G(F)^0` (`ParahoricBuildingData.rootGroup_le_simplyConnectedImage`).

`rationalCommonNormKernel_le_zeroSubgroup_of_diagonal`: the image `H` of `G(F)^0` in
`GL_N(F)` is normal (`ParahoricBuildingData.normal_zeroSubgroup`). For `N ≥ 2` it contains
`SL_N(F)` (`specialLinear_le_of_normal`); for `N = 1` the group `SL_1(F)` is trivial, and for
`N = 0` the whole group is trivial. A point `g` of `G(F)^1` is `M · diag(det g, 1, …, 1)` with
`M ∈ SL_N(F)` (`eq_toGL_mul_diagGL`), and the diagonal factor lies in `H` because `det g` has
valuation one.

`rationalCommonNormKernel_le_zeroSubgroup`: by the conjugacy of maximal split tori
(`maximalSplitTorusConjugacy`) there are `g ∈ G(F)` and an isomorphism of the datum's split
torus with the diagonal one compatible with conjugation by `g`. The transported datum
`D.basedTransport σ (innerIso g) h` satisfies the group axioms
(`KPBuildingDatum.SatisfiesGroupAxioms.basedTransport`), in particular the apartment axioms, and
has the same zero subgroup (`ZeroSubgroupDatum.zeroSubgroup_eq_of_datum`).
