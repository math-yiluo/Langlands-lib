# The rational cyclic weight filtration of a dynamic unipotent subgroup

Author: Worker 1423.

Helper module for the proof of
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`.
All declarations are in namespace `Langlands.GroupScheme.Dynamic.GradedCoordinates`.

## General topology

- `isOpenMap_of_continuous_section`: a map `q` from a topological group to an additive group,
  additive in the sense `q (a * b) = q a + q b`, with a continuous section `s` (`q ∘ s = id`),
  is open. Indeed `q '' W = s ⁻¹' (W * ker q)`, and `W * ker q` is open for open `W`.

## The filtration

For a smooth affine group `G` over a field `k` and a cocharacter `χ`:

- `rationalFiltration G χ r`: the rational points of
  `weightFiltration (AutomorphicAction.conjugation χ) (𝟙 _) (r + 1)`.
  `rationalFiltration_zero` identifies step `0` with the rational points of
  `Dynamic.unipotent χ`. `rationalFiltration_succ_le` and `rationalFiltration_le_zero` hold
  (`weightFiltration_antitone`).
- `fromBase`, `fromBase_toBase`: the inverse of `toBase (baseTest k)`.
- `mem_rationalFiltration_iff`: membership read in the model (`mem_weightFiltration_iff_modelPoint`).
- `rationalCut`, `rationalCut_mul`: the cut point of a rational point of `U(χ)`.
- `toBase_comp_mul`, `conj_mem_rationalFiltration`, `mem_normalizer_rationalFiltration`: a
  rational point `g` of the torus centralizer of `χ` normalizes every step. This is
  `conj_mem_weightSubgroup_of_hat_eq` for `constantFamily G g`.

## Coordinates

For graded polynomial coordinates `x` (weights `d i > 0`, `aeval x` bijective):

- `ratCoord G χ x p i`: the coordinate `x i` of the cut point of `p`.
- `ratCoord_mul`: on step `r`, the coordinates of weight `r + 1` are additive.
- `mem_rationalFiltration_iff_ratCoord`: `p` lies in step `r` iff its coordinates of weight
  `< r + 1` vanish.
- `ratCoord_conj`: on step `r`, conjugation by `g` acts on the coordinates of weight `r + 1`
  by the corresponding block of `conjMatrix` for `constantFamily G g`
  (`coord_cutConj_eq_sum`).
- `rationalFiltration_eq_bot`: step `N` is trivial if all weights are at most `N`.
- `coordPoint`, `coord_coordPoint`, `coord_coordPoint_val`, `ratPoint`, `ratPoint_mem`,
  `ratCoord_ratPoint`: the rational point with prescribed coordinates, through
  `rationalPointEquiv`, `modelPointEquiv` and the inverse of `aeval x`.
- `continuous_toBase_comp`, `continuous_ratCoord`, `continuous_ratPoint`: with the Library's
  `rationalPointTopology`, the coordinates are continuous, and so is `ratPoint`. This uses
  `rationalPointsAffineHomeomorph`, `continuous_coord_modelPoint`,
  `continuous_modelPointEquiv_symm` and `MvPolynomial.continuous_eval`.

## Provenance

Internal. This is the passage of the cyclic weight filtration of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8, to rational points and their topology.
