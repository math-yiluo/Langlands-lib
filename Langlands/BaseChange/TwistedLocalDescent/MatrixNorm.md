# The entrywise sup norm on matrices over an ultrametric field

Module `Langlands.BaseChange.TwistedLocalDescent.MatrixNorm`. Matrices carry the entrywise sup norm
(`Matrix.normedAddCommGroup`).

- `matrix_isUltrametricDist`: over an ultrametric field the sup norm on `M_n` is ultrametric.
- `matrix_norm_mul_le`: it is submultiplicative, `‖X Y‖ ≤ ‖X‖ ‖Y‖` (each entry of `X Y` is a sum
  of products bounded by `‖X‖ ‖Y‖`, and the ultrametric inequality bounds the sum);
  `matrix_norm_one_le`, `matrix_norm_pow_le`, `matrix_norm_map_eq` (an isometric map applied
  entrywise preserves the norm).
- `lowerLevel B t`: matrices whose nonzero entries go down at least `t` blocks;
  `mul_mem_lowerLevel`, `pow_mem_lowerLevel`, `eq_zero_of_mem_lowerLevel` (nothing goes down
  `B.length` blocks), `pow_length_eq_zero`: a strictly block lower matrix `Z` is nilpotent,
  `Z^{B.length} = 0`.
- `lowerInverse B Z = Σ_{t < B.length} (−Z)^t`, the inverse of `1 + Z` for strictly block lower `Z`
  (`one_add_mul_lowerInverse`, `lowerInverse_mul_one_add`, geometric series);
  `norm_lowerInverse_le`: `‖(1 + Z)⁻¹‖ ≤ 1` when `‖Z‖ ≤ 1`.
