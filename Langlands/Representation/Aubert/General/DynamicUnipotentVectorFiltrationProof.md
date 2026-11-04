# Proof of the vector filtration of a rational dynamic unipotent subgroup

Author: Worker 1423.

This module proves
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement` as
`Langlands.Aubert.General.RationalPointFamily.dynamicUnipotentVectorFiltration`, using the
helper modules `GroupScheme.Dynamic.UnipotentWeightFiltration`,
`GroupScheme.Dynamic.UnipotentGradedCoordinates`, `GroupScheme.Dynamic.UnipotentGradedTopology`,
`GroupScheme.Dynamic.UnipotentGradedLie`, `GroupScheme.Dynamic.UnipotentRationalFiltration`,
`GroupScheme.Rational.CyclicWeightCoordinates` and `GroupScheme.Rational.CyclicWeightConjugation`.

## Auxiliary lemmas

- `sum_filter_eq_sum_fin`: a sum over `{j | d j = s}` reindexed over `Fin (card …)` by
  `Fintype.equivFin`.
- `prod_range_det_toSquareBlock`: if all weights lie in `1, …, N`, the product over
  `r < N` of the determinants of the weight-`(r + 1)` blocks of a matrix is the product over
  the weights that occur; missing weights give empty blocks of determinant `1`.

## Proof of the statement

Let `G` be connected reductive over the nonarchimedean local field `k`, so smooth and affine.
Apply the Library's `exists_aeval_bijective_cyclicTail` to the corepresented model, to the
conjugation action of `𝔾_m` through `χ`, and to `r = 1`. This gives graded polynomial
coordinates `x i` of weights `dd i > 0` on the first cyclic weight subgroup. Let
`g = m ≫ iZ`; it commutes with `χ`.

- `J = centralizerMatrix …`. Then `det J = rationalCharacterEval δ m`, by
  `rationalCharacterEval_determinantCharacter` and `det_differential`. Also
  `det J = ∏_s det(block s)` (`det_conjMatrix`), so every block has nonzero determinant.
- `N` is the largest weight, `F r = rationalFiltration G χ r`, and `n r` is the number of
  coordinates of weight `r + 1`, indexed by `Fin (n r)`.
- `q r p` is the vector of coordinates of weight `r + 1` of `p`, and `L r` is the linear
  equivalence (`LinearMap.equivOfDetNeZero`) given by the reindexed weight-`(r + 1)` block.
- The conditions:
  - `F 0 = U(χ)(k)` is `rationalFiltration_zero`; `F N = ⊥` is
    `rationalFiltration_eq_bot`.
  - The descent is `rationalFiltration_succ_le`; normalization by `g` is
    `mem_normalizer_rationalFiltration`.
  - Additivity is `ratCoord_mul`. The kernel condition comes from
    `mem_rationalFiltration_iff_ratCoord` at steps `r` and `r + 1`.
  - Continuity is `continuous_ratCoord`.
  - Surjectivity and openness come from the continuous section `w ↦ ratPoint (v w)`. Here
    `v w` places `w` on the coordinates of weight `r + 1` and zeros elsewhere
    (`continuous_ratPoint`, `ratCoord_ratPoint`, `isOpenMap_of_continuous_section`).
  - The intertwining `q r (g p g⁻¹) = L r (q r p)` is `ratCoord_conj` after reindexing.
  - Finally, `∏_{r < N} det (L r) = ∏_{r < N} det(block (r + 1)) = det J`, which is
    `rationalCharacterEval δ m` (`prod_range_det_toSquareBlock`).

The topology of `RationalPoint k G.X` is the statement's `pointTopology`, which unfolds to the
Library's `rationalPointTopology` used by the helper lemmas.

## Provenance

The mathematics is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8 and
Proposition 2.1.8(1), as recorded in the statement's Markdown. The proof route is internal:
it uses one system of graded polynomial coordinates on `U(χ)` for all steps, the linear part of
conjugation in these coordinates for both the rational and the Lie computation, and an
explicit continuous section for openness.
