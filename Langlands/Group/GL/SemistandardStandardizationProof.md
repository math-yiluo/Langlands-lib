# Determinant proof of semistandard block standardization

`Langlands.glSemistandardStandardization.{uF}` proves the exact proposition
`Langlands.GLSemistandardStandardizationStatement.{uF}` from
`SemistandardStandardizationStatement`. Every rank is included, including
zero, and the original ordered block shape is retained. The theorem assumes
only the stated inclusion of actual split-component subgroups. It preserves
the arbitrary field universe and adds no topological or representation premise.

The implemented proof is elementary matrix algebra. It does not use a
classification or conjugacy theorem, and its determinant argument avoids a
separate dimension-counting theorem for simultaneous eigenspaces.

1. `GeneralLinear.BlockShape.exists_permutation_nonzero_entries` expands the
   determinant of an invertible matrix `g`. Since the determinant is nonzero,
   one summand is nonzero. Its permutation `s` satisfies `g (s k) k ≠ 0` for
   every coordinate `k`. This works for the empty matrix as well.
2. `Exponents.ConjugateBlockPair.offBlock_zero_of_semistandard` works over
   any characteristic-zero field. Fix a nonzero entry of the conjugator `c`
   in row `k` and a column of block `i`. Choose a block-scalar tuple equal to
   the unit `2` on block `i` and `1` elsewhere. The actual subgroup inclusion
   gives a coordinate diagonal matrix `D(b)` equal to `c D(a) c⁻¹`. Hence
   `D(b)c = c D(a)`. At the nonzero pivot, cancellation yields `b(k) = 2`.
   At a column of any other block, the same equation is `2x = x`, hence
   `x = 0`. The proof uses the published block-scalar matrix formulas and
   the singleton diagonal formula to make these entry equations explicit.
3. `GeneralLinear.BlockShape.exists_levi_of_offBlock_zero` proves that an
   invertible matrix whose off-block entries vanish is in the image of the
   actual Levi embedding. Vanishing below the diagonal first makes it an
   element of the block parabolic. Its published `leviProjection` supplies
   invertible diagonal blocks. Entrywise comparison, separately within a
   block and between distinct blocks, proves that their embedding is the
   original matrix. No inverse-block hypothesis is assumed.
4. `Exponents.ConjugateBlockPair.exists_permutation_standardizer` chooses
   the determinant permutation `s` and uses the actual permutation matrix
   for `s⁻¹` on the left of `c`. Its entry in row `x`, column `y` is
   `c (s x) y`. The pivot `c (s x) x` is nonzero, so step 2 kills every
   entry between distinct original blocks. Step 3 supplies the required
   product-Levi element.
5. The exact final theorem introduces the characteristic-zero instance for
   `F.Carrier` from its algebra over `Padic p`, then applies step 4. Thus the
   stronger characteristic-zero helper implies the specified p-adic target
   directly, without a change of universes or additional data.

These helper lemmas are derived within this proof module. Their provenance is
the displayed determinant, cancellation and block-projection argument, using
Mathlib and the published project definitions. No external literature theorem
is asserted to implement this proof. The proof establishes the explicit matrix
equation only; the downstream parabolic, Levi, split-component, character and
representation transport use separate published interfaces.
