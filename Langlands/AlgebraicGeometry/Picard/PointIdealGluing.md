# Gluing ideal sheaves on `X ×_R G` from natural families on affine points of `G`

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`. Let `π : X ⟶ Spec R` and `p : G ⟶ Spec R`.

- `ptMap_congr`, `range_ptMap`, `ptMap_snd`, `resAlgHom`, `specMap_resAlgHom`.
- `PointIdeals π p`: an admissibility predicate `P` on `B`-points `k` of `G` (for all
  `R`-algebras `B`) stable under base change, ideal sheaves `F k` on `X_B` for admissible `k`,
  natural in base change (`F_comp`), and such that every point of `G` has an admissible affine
  open neighbourhood (`cover`).
- `Adm`, `piece`, `pieceι`, `pieceIdeal`, `adm_of_le`, `comap_pieceIdeal_of_factor`,
  `range_pieceι`, `openCover`, `exists_lift_piece`, `snd_mem_of_factor`, `compat`: the pieces
  `X ×_R Spec Γ(G, O)` over admissible affine opens `O` cover `X ×_R G`, and the ideals `F` on them
  agree on overlaps.
- `exists_glued`: an ideal sheaf `W` on `X ×_R G` restricting to `F` on every piece (FLT
  `IdealSheafData.exists_comap_eq_of_openCover`).
- `comap_ptMap_of_factor`, `comap_ptMap`: `W.comap (ptMap k) = F k` for every admissible point `k`
  (local on `Spec B` through basic opens mapping into admissible affine opens).
