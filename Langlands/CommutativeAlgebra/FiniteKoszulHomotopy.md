# Generator homotopies for the finite subset Koszul differential

Author: Worker 1015.

This internal supporting construction defines exterior insertion by an index
`j` on the subset-coordinate modules of `FiniteKoszulComplex`. It applies to
any commutative ring `R` and any linearly ordered index type `ι`; the identities
involving the differential require `ι` to be finite.

`koszulAmbientInsertion j` sends a coordinate vector `x` to the vector whose
coordinate at `s` is zero unless `j ∈ s`. In that case it is
`koszulSign R s j * x (s.erase j)`. The theorem
`koszulAmbientInsertion_identity` proves
`d ∘ h_j + h_j ∘ d = a_j • id`, where `d` is the imported
`koszulAmbientDifferential a`. In the coordinate proof, the summand indexed
by `j` supplies `a_j * x(s)` using the shared `koszulSign_mul_self`
identity from [FiniteKoszulComplex](FiniteKoszulComplex.md). The other
summands cancel using the two insertion sign identities, after splitting
according to the relative order of the indices.

`finiteKoszulInsertion j n` restricts this insertion to the map from the
full function module on `n`-element subsets to the full function module on
`(n+1)`-element subsets. When `ι` is finite, these are the finite free modules
on the corresponding subsets. The theorem `koszulExtend_insertion` shows that its extension by
zero agrees with ambient insertion of the extended input. This follows
from the cardinality of erasing a member. The imported extension by zero
is injective, so the ambient identity gives the homogeneous identities:

- `finiteKoszulInsertion_identity`: on degree `n+1`,
  `d_(n+1) ∘ h_(n+1) + h_n ∘ d_n = a_j • id`.
- `finiteKoszulInsertion_identity_zero`: on degree zero,
  `d_0 ∘ h_0 = a_j • id`, because the ambient differential of a vector
  supported on the empty subset is zero.

These formulas use the unsigned chain differential and the signs already
fixed by `FiniteKoszulComplex`. The proof is an internal derivation from
those definitions. This file does not package a categorical complex or
homotopy, prove Koszul exactness, or prove the residue-resolution duality
statement. It supplies the linear identities needed for the generator
null-homotopies in that construction.
