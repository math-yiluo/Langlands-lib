# Assembly of the special unitary Hasse principle

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisAssembly`.

- `isAntihermitian_diagonal`: a diagonal matrix with alternating entries is antihermitian.
- `diagonal_eq_adjoinSkewLine`: a diagonal matrix of size `m + 1` is
  `adjoinSkewLine` of its upper left diagonal block and its last entry.
- `exists_diagonal_congr` (for an involution `τ` with `τ a ≠ a` for some `a`): an invertible
  antihermitian Gram matrix `H` is congruent, `P H P* = diagonal d`, to a diagonal matrix with
  nonzero alternating entries. The rows of `P` form the orthogonal basis of
  `AntihermitianForm.orthogonalBasis` for the form `AntihermitianForm.ofMatrix H`;
  `P` is invertible by `isUnit_of_mul_mul_matrix_eq`.
- `quaternionConjugation_ne_id`: the canonical quaternion conjugation is not the identity
  (it negates the alternating unit; characteristic zero).
- `suHasse_succ`: `SUHasse` in rank `m` (`m ≥ 1`) and proper Witt transitivity in rank
  `m + 1` over every field of characteristic zero containing `F` give `SUHasse` in rank
  `m + 1`: diagonalize `H`, apply `suHasse_adjoin` to the diagonal matrix written as an
  adjoined line, and transport back with `HasseFor.congr`.
- `suHasse_of_rankOne`: `SUHasse` in rank one and proper Witt transitivity in every rank at
  least two give `SUHasse` in every rank `m + 1`, by induction on `m`.
