<!-- MANUAL -->
# Diagonal determination of intersection-Levi characters over infinite fields

Lean module: `Langlands.AllFieldBZ.Representation.Geometric.IntersectionLeviDiagonalCharacterInfinite`
(hand-written, part of the all-field port).

## Purpose

The Library theorem `Langlands.Geometric.intersectionLeviDiagonalCharacterTheorem` (module
`Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof`) assumes `[CharZero F]`:
its proof conjugates a transvection by the diagonal scalar `2`. A nonarchimedean local field of
positive characteristic does not satisfy this hypothesis. This module proves the same conclusion
under `[Infinite F]` instead, which every nonarchimedean local field satisfies
(`Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.infinite`). The ported module
`Langlands.AllFieldBZ.Representation.Geometric.IntersectionLeviModulusBalance` uses it.

## Declarations

In namespace `Langlands.AllFieldBZ.Geometric.DiagonalCharacter`, for a field `F`:

- `scale_transvection_by i j hij c hc x`: with `d` the unit diagonal matrix whose `i`-th entry is
  `c ≠ 0` and whose other entries are `1`, `d * E_ij(x) = E_ij(c * x) * d`, where `E_ij(x)` is the
  transvection unit `transvectionUnit i j hij x` (`i ≠ j`).
- `character_transvection` (`[Infinite F]`): every group homomorphism `χ : GL_k(F) →* ℂˣ` sends every
  transvection to `1`.
- `character_GL` (`[Infinite F]`): a homomorphism `χ : GL_k(F) →* ℂˣ` that is `1` on every unit
  diagonal matrix is `1` everywhere.
- `character_pi_GL` (`[Infinite F]`): the same for a finite product `∏ i, GL_{d i}(F)`, assuming
  `χ` is `1` on all tuples of unit diagonal matrices.

In namespace `Langlands.AllFieldBZ.Geometric`:

- `intersectionLeviDiagonalCharacter_of_infinite F n B C w` (`[Field F] [Infinite F]`): for block
  shapes `B C` of `n` and a minimal double-coset representative `w`, let `I` be the intersection of
  the Levi subgroup of `B` with the `w`-conjugate of the Levi subgroup of `C`
  (`General.intersectionIn (B.leviSubgroup F) (C.leviSubgroup F) (GeneralLinear.permutation n F w.val)`).
  Every homomorphism `χ : I →* ℂˣ` that is `1` on each element of `I` whose matrix is diagonal is
  `1` on all of `I`. This is the Library statement
  `Langlands.Geometric.IntersectionLeviDiagonalCharacterStatement` with `[CharZero F]` replaced by
  `[Infinite F]`.

## Proof

- `scale_transvection_by`: entrywise comparison of the two matrix products.
- `character_transvection`: since `F` is infinite, choose `c ∉ {0, 1}`. Put `x = y / (c - 1)`.
  Then `E_ij(c * x) = E_ij(x) * E_ij(y)`, because `c * x = x + y`. Apply `χ` to
  `scale_transvection_by` and use that `ℂˣ` is commutative:
  `χ(d) χ(E(x)) = χ(E(x)) χ(E(y)) χ(d)`, and cancellation gives `χ(E(y)) = 1`.
- `character_GL`: Mathlib's `Matrix.diagonal_transvection_induction_of_det_ne_zero` writes every
  invertible matrix as a product of diagonal matrices and transvections. `χ` is `1` on the diagonal
  factors by hypothesis and on the transvections by `character_transvection`.
- `character_pi_GL`: reduce to each factor with the Library lemma
  `Langlands.Geometric.DiagonalCharacter.character_pi`, then apply `character_GL` to `χ` composed
  with the inclusion of the `i`-th factor.
- `intersectionLeviDiagonalCharacter_of_infinite`: follows the Library proof of
  `intersectionLeviDiagonalCharacterTheorem`. The Library lemma `exists_standardIntersections`
  gives a refinement `S` of the blocks of `B`. The composite isomorphism `e` (`refinedLeviEquiv F B S`,
  then `MulEquiv.subgroupCongr`, then `DiagonalCharacter.sourceActualEquiv B C w.val`) identifies
  the product over `i` of the refined Levi groups `(S i).Levi F` with `I`. Put `ψ = χ ∘ e`. By the
  Library lemma `leviEmbedding_diagonalUnit`, `e` sends tuples of unit diagonal matrices to
  diagonal matrices, so `ψ` is `1` on them. The Library lemma `DiagonalCharacter.character_pi`
  reduces `ψ = 1` to each factor `(S i).Levi F`, which is a finite product of general linear
  groups, and there `character_pi_GL` applies. Hence `χ = ψ ∘ e⁻¹ = 1`.

## Provenance

Written by Worker 71. It uses the same reduction as the Library proof (Library module
`Langlands/Representation/Geometric/IntersectionLeviDiagonalCharacterProof.lean`), with a
different argument for the vanishing on transvections, so that it holds in every characteristic.
