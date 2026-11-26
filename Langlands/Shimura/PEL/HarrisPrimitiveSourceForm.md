# The primitive pairing of the fixed Harris source lattice

For the arithmetic and signature data of `HarrisIntegralPairing`,
`harrisHodgePELPairingContent` chooses an integer generator \(c\) of the
ideal of values of the existing integer Harris pairing on its existing
lattice. The pairing is nondegenerate and the lattice has positive rank,
so \(c\ne 0\). `harrisHodgePELPrimitivePairing` is its division by \(c\)
on that same lattice. Multiplication by \(c\) recovers the original
integer pairing, and the divided pairing is alternating and nondegenerate.
Its values span the unit ideal because the generator \(c\) lies in the
integer span of the original pairing values. Dividing this span relation
by \(c\) expresses \(1\) in the span of the divided values.

`harrisHodgePELPrimitiveAdelicForm` scales the original rational adelic
form by the diagonal rational scalar \(c^{-1}\). On pure tensors
\(1\otimes x\) and \(1\otimes y\) from the integral Harris lattice,
its value is the divided integer pairing. Bilinearity then gives
integrality on the entire integral finite-adele span. Multiplying the
rescaled adelic form by \(c\) recovers the form used by the original
Weil frames.

The content division is a derived arithmetic construction on the lattice
of `HarrisIntegralPairing`. Its source context is the nondegenerate
involution-compatible alternating form in Kottwitz, *Points on Some Shimura
Varieties over Finite Fields*, §5, printed p. 389 (PDF p. 17).
The global integer lattice and its content are defined using the
Library's actual normalized Harris data.

Source `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`,
§5, printed p. 389 (PDF p. 17).
