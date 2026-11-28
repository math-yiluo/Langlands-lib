# The coarse corner as a conjugate of a standard unipotent radical

Module `Langlands.BushnellKutzko.SplitTypeJacquet.CoarseCut`.

- `not_subsingleton_coinvariants_of_le`: if `N' ≤ N` and the Jacquet module of a representation
  along `N` is nonzero, so is its Jacquet module along `N'`, since the quotient map onto the
  coinvariants of `N` factors through those of `N'`.
- `mem_coarseN_of_entries`: a matrix that agrees with the identity outside the late-early corner
  lies in `coarseN F blk j`.
- `exists_perm_late`: there is a permutation `σ` of the coordinates sending the first `b`
  coordinates onto the late ones, where `b` is the number of late coordinates.
- `conjugateUnipotent_le_coarseN`: for `0 < b < n`, the conjugate by `permutation σ` of the
  unipotent radical of the two-block shape `(b, n - b)` (the Library's `twoBlock`) lies in
  `coarseN F blk j`. The entries of the conjugate are those of the original element at
  `σ⁻¹`-permuted positions (`permutation_conjugate_entry`), and elements of that radical are block
  unipotent (`isBlockUnipotent_of_mem_cutShape`).
