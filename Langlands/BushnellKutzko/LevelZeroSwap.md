# Matrix identities on two blocks

The elementary elements of `GL (Fin f ⊕ Fin f) F` for the transposition
calculation are `upperU X = [[1, X], [0, 1]]`,
`lowerU Y = [[1, 0], [Y, 1]]`, `diagU A D = [[A, 0], [0, D]]`, and
`swapU = [[0, 1], [1, 0]]`. For a square matrix `T` with `T * T = 0`,
`unipU T hT` is the unit `1 + T` in `GL (Fin f) F`.

The following identities come from block-matrix multiplication.

- The transposition squares to the identity and conjugates `lowerU Y` to
  `upperU Y`. Upper unipotents multiply by adding their upper right blocks.
- For invertible `X`, `upperU_eq_of_isUnit` gives
  `upperU X = lowerU X⁻¹ * swapU * diagU (-X⁻¹) X * lowerU X⁻¹`.
- When `Z * E = 0`, `lowerU_mul_upperU` gives
  `lowerU Z * upperU E = upperU E * diagU (unipU (-(E * Z))) 1 * lowerU Z`.
- Conjugating `upperU E` by `diagU A D` gives `upperU (A * E * D⁻¹)` by
  `diagU_upperU_conj`.

The invertible and singular residue cases use the second and third
identities respectively. [Transposition step](LevelZeroSwapStep.md)
