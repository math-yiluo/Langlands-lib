# Spectral bounds on multiplicative rational-point families

This internal helper makes the trace argument in Kaletha–Prasad, Lemma 2.2.11
(printed pages 72–73, PDF pages 103–104), apply to the geometric image of the
original field's rational points. It does not assert coefficient bounds at every
point over an algebraic closure.

`HasFullRationalMatrixSpanOn rho B` says that the matrices of the specified
actual rational points span the full matrix algebra. If `B` is closed under
multiplication and its characteristic coefficients lie in the valuation ring,
`hasBoundedRationalEntries_of_fullSpanOn` bounds its entries. The monoid-family
version takes the span of the range of `rho.rationalMatrix (alpha i)` directly.
The characteristic trace formula gives the trace bound (with an explicit empty
coordinate case), and multiplication stays inside the family. The published
trace-probe theorem then gives one nonzero bound for all entries.

The remaining lemmas pass these entry bounds through the actual block diagonal
direct sum and then to its actual scheme-point image in the general linear
group. On an inverse-stable set, the identity representation of that target is
closed, so the previously proved entry/inverse-entry coordinate argument bounds
every regular function there. No closedness of the original coefficient map is
required for this image bound. These are bounds for the specified sets, not an
unconditional boundedness or density theorem.
