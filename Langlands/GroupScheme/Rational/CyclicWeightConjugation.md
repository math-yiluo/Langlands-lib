# Conjugation by a torus-fixed point on cyclic weight subgroups

Author: Worker 1423.

Helper module for the proof of
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`.
All declarations are in namespace `Langlands.GroupScheme.Corepresented`.

## Natural endomorphisms

- `coord_natural`: a natural family `c` of maps on the points of a corepresented functor acts on
  coordinates by precomposition with `κ = coord (c (univ e))`:
  `coord (c x) = (coord x).comp κ` (Yoneda, via `eq_map_univ` and `coord_map`).
- `isHomogeneous_coord_natural`: if `c` also commutes with the torus action, then `κ` maps
  homogeneous elements of weight `m` to homogeneous elements of weight `m`. Indeed `c` commutes
  with the twisted point `hat`, and `rho = coord (hat univ)`.

## Conjugation by a fixed family

Let `z A ∈ F(A)` be a family of points, natural in `A` (`hzn`) and fixed by the torus action
(`hzf`). This is the model of a rational point commuting with the torus.

- `hat_eq_of_fixed`: the twisted point of `z A` is constant.
- `conj_mem_weightSubgroup_of_hat_eq`: conjugation by a point with constant twisted point
  preserves every weight subgroup. The twisted point comes from the constant subalgebra
  (`constSupported`), which normalizes the Library's kernel subgroups
  (`conj_mem_kerSubgroup`, `weightCondition_iff`).
- `TorusAction.act_inv`: the torus acts by group automorphisms.
- `cutConj e σ hzn hzf P A`: conjugation by `z A` on the points of the weight subgroup for `P`.
  `cutConj_natural` and `cutConj_act` give naturality and commutation with the torus.
- `conjCoord`: the coordinate endomorphism `κ` of `cutConj`. `coord_cutConj` and
  `isHomogeneous_conjCoord` are the two previous general statements.

## The linear part

For graded polynomial coordinates `x` (weights `d i • a`, `d i > 0`) on the first cyclic
weight subgroup:

- `exists_conjCoord_eq_aeval`, `conjPoly`: `κ (x i)` is the image of a weighted homogeneous
  polynomial of degree `d i` in `x`. This uses `decompose_aeval`, since `κ (x i)` is homogeneous
  of weight `d i • a`.
- `conjMatrix`: the matrix of linear coefficients `J i j = coeff (single j 1) (conjPoly i)`.
- `coord_cutConj_eq_sum`: on points of `U_r`, for `d i = r`,
  `coord (cutConj u) (x i) = ∑_{d j = r} J i j * coord u (x j)`. This combines
  `mem_weightSubgroup_iff_coord_eq_zero` with `aeval_eq_sum_of_isWeightedHomogeneous`.
- `conjMatrix_eq_zero_of_ne`, `conjMatrix_blockTriangular`: `J i j = 0` unless `d j = d i`.
- `det_conjMatrix`: `det J = ∏_{s ∈ image d} det (J.toSquareBlock d s)` (Mathlib's
  `Matrix.BlockTriangular.det`).

## Provenance

Internal. Mathematically this is the statement that the centralizer of `S` acts linearly on
the vector-group quotients `U_{A^j}(G)/U_{A^{j+1}}(G)`, and preserves their unique
`S`-equivariant linear structure (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed.,
Lemma 3.3.8). Here it is proved in graded coordinates.
