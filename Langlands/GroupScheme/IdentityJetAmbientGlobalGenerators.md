# Actual global ambient generators of identity jets

Let `G` be an affine group over `Spec R`, let `b : S → Spec R`, and
let an actual relatively affine group `H` over `S` map to `G_S`.
The fixed affine coordinates of `G` modulo the `(n+1)`st augmentation
power give actual functions on the identity jet of `H`.
`ambientGlobalGenerator` packages this map as an `R`-linear family in
actual global sections of the jet module, including when `S` is nonaffine.

The proof checks scalar multiplication on a representative of the
quotient class. The ambient scalar function is the actual pullback
of the base scalar to `H`. Its restriction to the actual jet acts
through the jet projection on the pushed-forward structure module.
The underlying function is exactly `ambientQuotientCoordinates`.

On every affine open of `S`, `globalFamilyTensorMap_ambientGlobalGenerator`
identifies extension of this global family to the open's section ring
with the existing `ambientTensorCoordinates`. On a pure tensor both maps
restrict the same global function and multiply it by the same coefficient.
Tensor induction gives the equality of linear maps.

This is an internal consequence of the actual function-pullback and
truncated-coordinate formulas. The global family gives the jet summand
of the prescribed stabilized generators on the parabolic quotient and
retains the existing affine tensor map used in the kernel comparison.
