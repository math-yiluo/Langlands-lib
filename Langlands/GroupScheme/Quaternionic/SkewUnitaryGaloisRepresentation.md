# Local coboundary data and local representation of diagonal values

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisRepresentation`.

- `IsCoboundaryAt τ H c K` (for a field `K ⊇ F`) is the proposition: for every finite Galois
  extension `M` of `K` containing `L` (compatibly over `F`) there is `b ∈ suGroup τ H M` with
  `c (s|_L) = b * s(b)⁻¹` in `M` for all `s ∈ Gal(M/K)`. It expresses that the image of the
  class of `c` in `H¹(K, SU(h))` is trivial, computed on a Galois extension.
- `IsLocallyCoboundary τ H c` (over a number field) is `IsCoboundaryAt` at the completion of
  every infinite place (`w.Completion`) and every finite place
  (`Global.FiniteCompletion F v`).
- `adjoint_gramOver`, `gramOver_mul`, `matrixSesqBilin_row`: `1 ⊗ (·)` commutes with the
  conjugate transpose and products; the diagonal entries of `P G P*` are the values of the
  form `G` on the rows of `P`.
- `GramDescent.gram_antihermitian` (`2` invertible) and `GramDescent.gram_isUnit`: the
  descended Gram matrix is antihermitian and invertible when `H` is.
- `GramDescent.exists_represent_over` and `GramDescent.isLocallyRepresented`: with coboundary
  data at `K`, the descended Gram matrix `H'` represents each diagonal entry `H i i` over `K`
  (row `i` of the local isometry); over a number field with local coboundary data everywhere,
  `H'` represents `H i i` at every place (`τ.IsLocallyRepresented`). The finite Galois
  extension `M` is supplied by `CentralSimpleUnits.exists_finiteGalois_over_baseChange`.
