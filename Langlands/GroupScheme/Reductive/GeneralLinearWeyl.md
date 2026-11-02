# Permutation matrices normalize the diagonal torus of `GL_n`

Worker 274.

This is a helper module for the proof of `GeneralLinearRootDatumStatement`. It realizes
the permutation action of `S_n` on characters by normalizing points of `GL_n`
(Milne, Example 21.40, printed p.436, PDF 452: conjugation by a permutation
matrix permutes the diagonal entries).

- `permMatrix A w` is the permutation matrix with `P_w e_b = e_{w b}`, and
  `permGL A w` is the same matrix as an invertible matrix with inverse
  `P_{w⁻¹}` (`permMatrix_mul`, `permMatrix_one`). It is preserved by ring
  homomorphisms (`map_permGL`).
- `permuteCoords M w` is the coordinate permutation `t ↦ (c ↦ t (w⁻¹ c))` on
  families indexed by `ULift n`. `permGL_mul_diagonalTorusUnits` and
  `permGL_conj_diagonalTorusUnits` give `P_w diag(t) P_w⁻¹ = diag(t ∘ w⁻¹)`.
- `torusPerm R w` is the automorphism of the commutative split torus permuting
  the coordinates on points. It is built from the published `isoOfPoints`, and
  the lemmas `pointsEquiv_comp_torusPerm_hom` and `pointsEquiv_comp_torusPerm_inv`
  give it on points. `single_comp_torusPerm_inv` shows that its inverse sends the
  coordinate cocharacter at `c` to the one at `w⁻¹ c`.
- `permPoint R w` is the base point of `GL_n` with matrix `P_w`. Its restriction
  to any test scheme has matrix `P_w` (`pointsEquiv_constantPoint`,
  `pointsEquiv_constantPoint_permPoint`). `isNormalizingPoint_permPoint` shows
  that it normalizes the diagonal torus through `torusPerm R w`. The proof uses
  the published `comp_innerIso_hom` and the conjugation formula above.
- Over a field, `characterAut_torusPerm` shows that `χ ↦ (torusPerm w)⁻¹ ≫ χ` is
  `permutationAction n k w`. Both sides are compared in the coordinates of
  `characterLatticeEquiv`, using `single_comp_torusPerm_inv`.
  `permNormalizer k w` is the corresponding element of the normalizer.
  `weylAction_permNormalizer` and `range_permutationAction_le_weylImage` give
  `range (permutationAction n k) ≤ weylImage (diagonalTorus n k)`.
