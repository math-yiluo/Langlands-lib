# Character independence on strictly decreasing weights

`linearIndependent_strictWeightCharacters` proves that the characters of the
integer weight lattice `Fin n → ℤ`, with values in a commutative domain, are
linearly independent as functions on the strictly decreasing weights.
`strictWeightCharacterCoefficients_eq` recovers finitely supported coefficients
from evaluations on these weights multiplied by a common nonzero scalar that
can vary with the weight.

The proof first restricts the characters to the submonoid of weakly decreasing
weights. Given an integer weight `x`, multiply the strictly decreasing slope
`i ↦ -i` by `2 * ∑ i, |x i| + 1` to obtain a weakly decreasing weight `z` for
which `x + z` is also weakly decreasing. Two characters agreeing on the
submonoid then agree at `x` by multiplicativity and cancellation of their
common nonzero value at `z`. Applying Mathlib's `linearIndependent_monoidHom`
gives independence on this submonoid. Adding the slope `i ↦ -i` to a weakly
decreasing weight gives a strictly decreasing weight. In any finite relation
this translation multiplies each coefficient by the corresponding character
value at the slope. Those values are nonzero because the characters on the
lattice send inverses to multiplicative inverses.

This internal lemma supplies the independence step on the domain of regular
weights used in Henniart–Lemaire, I.5.5, printed pp. 37–38 (PDF pp. 45–46).
