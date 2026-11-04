# Positive tensor powers and their line stabilizers

This internal construction supports the tensor cancellation step for normal
subgroup kernels. The parameter `r` denotes the positive degree `r + 1`.
All coefficient calculations work over arbitrary commutative rings, and the
representation statements hold on all scheme tests over an arbitrary affine base.

`PositiveTensorIndex n r` recursively indexes the tensor power, with its finite
type and decidable equality instances. `positiveTensorVector` is the repeated
pure tensor of a vector, and `positiveTensorDiagonal` repeats a coordinate.
The coefficient map, normalization and scalar lemmas follow by induction.

`exists_unit_smul_of_positiveTensorVector` proves that a unit multiple of a
normalized repeated tensor detects the original line. In positive degree
greater than one, it multiplies the remaining transformed tensor factors by
the inverse scalar and applies the published normalized pure tensor
cancellation lemma. This proof also applies to rings with nilpotents.

`positiveTensorPower` is an actual group scheme representation, obtained by
iterating the published tensor homomorphism. It commutes with restriction.
The point matrix formula follows inductively from the Kronecker action formula.
Together these give `positiveTensorPower_preserves_line_iff`: a point preserves
the tensor power line exactly when it preserves the original line, provided
the original vector has a coordinate equal to one.

Over a field, for any affine group scheme, `characterUnit_nsmul` identifies the
unit of a natural multiple character with the power of its unit.
`positiveTensorPower_characterSpace` then sends a vector of character `χ`
to its repeated pure tensor, of character `(r + 1) • χ`. Its proof evaluates
the affine action formula at the universal point and uses the scalar formula.
No reducedness or smoothness hypothesis occurs.

The mathematical provenance is the elementary tensor line stabilizer step in
Milne, *Algebraic Groups* (2017), Corollary 4.29 (printed p. 95, PDF p. 111).
The official erratum replaces the proof's tensor target `W` by `V'`; the
present module uses actual ambient tensor representations throughout.
The recursive coordinate construction and normalized vector formulation are
internal implementation choices. This module proves no existence theorem for
inverse characters or quotient group schemes.
