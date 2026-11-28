# Transitivity of the open-cell integrals for the block sizes `(1, d + 1, t + 1)`

Module `Langlands.Representation.Shahidi.OpenCellThreeBlockFubini`, namespace
`Langlands.Shahidi.OpenCell`.

## Main result

`jacquetFunction_threeBlock`: for `ψ` of conductor `𝒪`, all parameters `a₁`, `a'`, `c` and all
degrees `D`, `e₁`,

`J_(d+2,t+1)[(δ^(1/2) J_(1,d+1)[(fullΦ a₁ a' 0)_(e₁)] ⊗ W°(·; c))_D](1)
  = J_(1,d+t+2)[(δ^(1/2) W°(·; a₁) ⊗ J_(d+1,t+1)[(fullΦ a' c 0)_(D-e₁)])_(e₁)](1)`.

## Proof

By the unfolding lemmas of `Langlands.Representation.Shahidi.OpenCellThreeBlock`, the left side is
`∫_Y ∫_z H(Y, z)` and the right side is `∫_y ∫_(Y'') H'(Y'', y)`, with
`H(Y, z) = conj ψ(Y_(t,0)) conj ψ(z_last) leftSection(diag(w' u'(z), 1) w u'(Y))` and `H'` the
analogue for `rightSection`. By `leftSection_eq_rightSection`, `reindex_threeBlock`
(`Langlands.Representation.Shahidi.OpenCellThreeBlockCoordinates`) and the kernel identities
`kernel_headColumns`, `kernel_shearColumn`, `H = H' ∘ threeBlockChange`. The function `H` is
integrable on the product: it is continuous (a right `GL(𝒪)`-invariant function is locally
constant, `continuous_of_mul_integral`), for each `Y` it is a constant times the Jacquet
integrand of a degree piece (`exists_kernel_mul_liftFunction_eq`), which is integrable, and
`Y ↦ ∫ ‖H(Y, z)‖ dz` is lattice-periodic and vanishes outside the depth-`D` classes, hence
integrable. Fubini (`integral_prod`, `integral_prod_symm`) and the measure-preserving change of
variables `threeBlockChange` give the identity.

## Provenance

Derived; this is the factorization of the long intertwining integral of a three-block
parabolic through the two intermediate parabolics, carried out on degree pieces so that every
integral is over a compact set.
