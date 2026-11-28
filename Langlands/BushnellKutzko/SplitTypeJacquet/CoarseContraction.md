# The coarse contraction

Module `Langlands.BushnellKutzko.SplitTypeJacquet.CoarseContraction`. Here `F` is a field with
a valuative relation; the last two results assume that `F` is a nonarchimedean local field.

For a uniformizer `ϖ` of `F` (an irreducible element of `𝒪[F]`), `aElt blk j hϖ` is the
diagonal matrix with entry `ϖ` at the late indices (`j ≤ blk p`) and `1` at the early ones; in
coarse block form it is
`leviHom (ϖ, 1)` (`coarseReindex_aElt`), so it lies in `coarseM` and centralizes it
(`aElt_inv_conj_levi`). Conjugation by `aElt` multiplies the corner of an element of `coarseN` by
`ϖ` (`aElt_conj_upper`, and `aElt_pow_conj_upper` for powers), and conjugation by its inverse
multiplies the corner of an element of `coarseNbar` by `ϖ` (`aElt_inv_conj_lower`).

`exists_pow_mul_lt_one`: for every `c ∈ F`, `ϖ^s c` lies in the maximal ideal for all large `s`.

`coarse_isCompressionContraction`: for an open subgroup `K` equal to `J1 F blk`, the element
`aElt` is a compression contraction (`IsCompressionContraction` of the module
`Langlands.BushnellKutzko.BundledJacquetCompression`) relative to `(coarseN, coarseM, coarseNbar)`:
`coarse_factor` gives the factorization (the middle factor of an element of `J1` again lies in
`J1`), conjugation contracts `K ∩ coarseN` and `K ∩ coarseNbar` in the required directions, and
every element of `coarseN` is carried into `J1` by conjugation with a power of `aElt`.
