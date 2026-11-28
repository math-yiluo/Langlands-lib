# Finite cutoffs for a change of the Iwasawa compact

The cutoff formula uses the compact and its height map from Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series* (2024), §2.1, p. 190,
and the inducing twist from §2.2, p. 191. These are pages 4–5 of the retained
journal PDF `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.

For an infinite conjugating point `s` with `s K∞ s⁻¹ = L∞`, the difference
`H_K(gs) − H_L(g)` equals `H_{sKs⁻¹}(g) − H_L(g) + H_K(s)`.
`exists_cutoff_family` uses `finite_range_height_sub` and
`height_sub_pair_eq_of_infinite_eq` to index the distinct values and show
that each fibre is a clopen set in the finite coordinate. Archimedean right
translation and multiplication by the finite-coordinate indicator preserve
automorphy for the new compact. The difference is invariant under left
multiplication by the parabolic. Thus the cutoff also preserves split-component
equivariance, and `parameterTwist_cutoff` expresses the translated twist as a
finite sum for the new compact with exponential coefficients.

`squareIntegrable_cutoff` compares weighted squares on the common discrete
parabolic quotient. The source weight shifted by the negative height
difference agrees with the target weight on that fibre. The source weighted
square is integrable, and the weighted target square is bounded in norm by
its right translate. The converse for weighted squares then yields the
canonical Levi integrability condition for the cutoff.

`inducedInnerProduct_eq_sum_cutoff` partitions the same quotient integral
by the height fibres. Each target pairing uses a shift of its height weight
by the value of the fibre. `inducedInnerProduct_shift` absorbs this shift,
so the resulting sum recovers the inducing pairing for the source compact.
`inducedInnerProduct_cutoff_ne` gives zero for distinct fibres, and
`coefficient_mul_star_of_imaginary` gives unit modulus for the diagonal
exponential at an imaginary parameter. The inducing pairing is the one
from Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series* (2011), §2, p. 311. The retained volume PDF
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` has SHA-256
`760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
