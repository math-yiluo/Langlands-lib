# Special unitary matrices as actual fixed points in SL3

This internal construction works over every commutative ring `A` equipped with the actual involutive ring automorphism `c.bar`. It uses the existing Gram matrix `J = [[0,0,1],[0,-1,0],[1,0,0]]` and the existing determinant-one Hermitian isometry subgroup of GL3. No characteristic or field hypothesis is imposed.

`weylSpecialLinear` is the actual matrix `J` in SL3. Its determinant is one and its square is the identity. `conjugateTransposeSL c` takes the actual conjugate transpose of a determinant-one matrix: determinant compatibility with ring maps and transpose ensures that the result still has determinant one. Conjugate transpose fixes the identity and `J`, reverses multiplication, commutes with inversion, and applying it twice recovers the matrix.

The monoid homomorphism `unitaryTwist c` sends `g` to `J * conjugateTransposeSL c (g⁻¹) * J`. Reversal by inversion and by conjugate transpose cancels, and `J * J = 1` proves multiplicativity. The identity `conjugateTransposeSL c g * J * unitaryTwist c g = J` follows by reassociation and cancellation. Consequently `unitaryTwist c g = g` holds exactly when the underlying matrix preserves the specified Hermitian form. The reverse implication cancels the invertible left factor in that identity.

`twistFixedSubgroup c` is the equalizer subgroup of this actual endomorphism and the identity on SL3. The multiplicative equivalence `fixedSpecialUnitaryEquiv c` identifies it with `specialUnitarySubgroup c` in GL3 through the usual `Matrix.SpecialLinearGroup.toGL` inclusion. Its inverse uses the actual determinant-one equation to regard the same GL3 matrix as an SL3 matrix. The form-preservation equation is unchanged, and both inverse laws preserve the underlying matrix.

For any ring homomorphism `f : A →+* B` commuting with the two specified involutions, coefficient change takes `J` to `J` and commutes with conjugate transpose and with `unitaryTwist`. The Lean proof checks equality entrywise for the transpose and then uses the special-linear coefficient homomorphism's multiplication and inversion laws. The coefficient universes may differ.

These are derived matrix constructions, with provenance in the imported concrete SU3 matrix definitions and elementary group identities. This unit does not yet construct a represented group scheme, identify its rational points, or compare the coordinate root ranges with actual parabolic radicals. Those comparisons and the unrestricted local Kneser–Tits theorem remain open.
