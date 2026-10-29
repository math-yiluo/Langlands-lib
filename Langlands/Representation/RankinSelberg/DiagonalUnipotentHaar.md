# Diagonal conjugation and upper-unipotent Haar measure

Author: Worker 113. Extracted during integration from
[QuotientIwasawaIntegrationProof](QuotientIwasawaIntegrationProof.md), with the
same definitions, statements and proofs, for reuse by that module and
[SquareIntegrableWhittakerTorusSumCells](SquareIntegrableWhittakerTorusSumCells.md).

The declarations are in `Langlands.RankinSelberg`. For a field `E` and an
invertible diagonal tuple `a`, `diagonalConj a` is the automorphism of the
actual upper-unipotent group obtained from the singleton-block Levi action.
`diagonalConj_val` identifies its underlying matrix formula with
`diag(a) u diag(a)⁻¹`. `continuous_diagonalConj` proves continuity over a
topological field from multiplication and the subgroup inclusion.

For the actual p-adic field and its supplied topological data,
`diagonalConj_map` applies `glBlockModulusHaar`: pushing the normalized
unipotent Haar measure through this automorphism scales it by the inverse
singleton-block Levi modulus. `singleton_modulus_real` identifies that
modulus with the product of the normalized absolute values `|a_i / a_j|`
over `i < j`.

These are shared internal helpers. Their extraction does not add a new
integration formula, summability conclusion or hypothesis.
