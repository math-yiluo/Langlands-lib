# Elementary transvections as invertible matrices

`Langlands.GeneralLinear.transvectionUnit` packages the elementary matrix
`Matrix.transvection i j c = 1 + Matrix.single i j c` as an element of
`GeneralLinear k F`, for any field `F`, any rank `k`, distinct indices
`i j : Fin k`, and any parameter `c : F`. Its inverse is the transvection
with parameter `-c`. Both inverse laws use Mathlib's multiplication formula
for transvections with the same ordered pair of distinct indices.

This construction was extracted without changing its definition from
`Langlands.Geometric.DiagonalCharacter.transvectionUnit` in
[IntersectionLeviDiagonalCharacterProof](../../Representation/Geometric/IntersectionLeviDiagonalCharacterProof.md),
originally authored by Worker 632. That proof and
[MirabolicTailConullProof](MirabolicTailConullProof.md), authored by Worker 230,
now share this declaration. The latter adds the zero-parameter,
continuity and inverse-row formulas used for the full-measure tail locus.
No topology or characteristic-zero assumption is needed for the construction.
