# Actual first-rectangle support through reversed duality

This derived internal support lemma concerns the actual five-block matrix in
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions* (1983),
§4.10(2), printed p. 419 (registered source `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The source supplies the matrix and its reversed-dual functional-equation
context; it does not separately state this auxiliary uniform support lemma.
The proof combines the published actual dual-matrix identity and the
second-rectangle support theorem.

Fix a p-adic field, a unitary additive character, positive block ranks
`a = m 0 + 1`, `b = m 1 + 1` with sum `t + 1`, and natural numbers `j,k`
with `r = t + (j + k + 1)`. Let `π` be any smooth complex representation
of `GL_(r+1)`, `ell` any supplied Whittaker functional, and `W` an element
of its actual coefficient model. The field and representation carrier
universes are independent. There is no irreducibility, genericity, or
nonzero-functional premise, and either complementary dimension may be zero.

`IsLeviFirstRectangularSupport` says that `C` is compact and contains

`(-x.transpose) * (weylLong a * inverseTranspose a (B 0) * weylLong a).val`

whenever `W` is nonzero at `matrix h hr (leviEmbedding B * c) x y`,
for every actual Levi element `B`, every `c ∈ integralOpen F t`, and every
pair of rectangles `x,y`. In particular, this is a support condition on
an explicitly transformed first rectangle, with its exact multiplication
order; it does not assert that the unscaled rectangle lies in a fixed
compact set. The theorem `exists_levi_first_rectangular_support` produces
one such set before quantifying over both blocks, both rectangles and `c`.

The algebraic helper `reversed_index_rev` checks the two consecutive
block offsets by finite-index arithmetic. As in the existing reversed
shape calculations, long reversal exchanges the two blocks and reverses
their internal indices. The entrywise theorem
`weyl_inverseTranspose_levi` then identifies the actual reflected Levi
blocks as `weylLong * inverseTranspose (B i.rev) * weylLong`. The existing
`TwoBlockDeformation.inverseTranspose_mem_integralOpen` theorem supplies
preservation of the actual integral subgroup.

For the support proof, transform `W` by
`translatedFirstDualModelEquiv` using `rightWeyl hr`. This is an element
of the inverse-transpose coefficient model, whose representation remains
smooth. Apply `exists_levi_second_rectangular_support` to that model with
the two block ranks and `j,k` exchanged. At `g = leviEmbedding B * c`,
the transformed group argument is `weylLong * inverseTranspose g`.
Its Levi part is the reflected Levi above and its right integral factor
is `weylLong * inverseTranspose c`; the two intervening Weyl matrices
cancel. Use the signed reversed transposes of `y,x` for the dual
rectangles. The full published `twoBlockDominantDualMatrix` equality
identifies the transformed coefficient evaluation with the original
one, preserving nonvanishing. Finally the reversed dual second rectangle
is exactly `-x.transpose`, giving the displayed compact coordinate.
All statements retain the actual group matrices and empty dimensions.
Rectangle volumes, cone estimates, integrability and the Laurent identity
are separate obligations.
