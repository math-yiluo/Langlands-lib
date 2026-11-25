# Real block exponent comparison from pair factors

`RealPairFactorExponentComparisonStatement` compares two finite lists of
certified real Weil-group blocks. Suppose that the two pair-factor
denominators agree as functions against each singleton block of real
exponent zero. If every block in the second list has real exponent
strictly above a given real number, then so does every block in the first.

This is a derived statement about the Library's `RealBlock.tensor`,
`realPairLFactor`, and `realBlockExponent`. A character can be tested with
the zero-exponent character of the same parity. An induced block can be
tested with the zero-exponent induced block of the same weight. The
conjugated summand in the latter tensor product has weight zero. Each
test places a pole at the negative of the original complex exponent.
The block pole criteria are recorded in `realLFactor_isPole` and the
opposite list's regularity criterion in
`realPairLFactorRightHalfPlaneRegularity`.

The comparison applies in particular at the threshold \(-1/2\) used for
the real case of Getz–Hahn, *An introduction to automorphic representations*
(2024), §11.5, printed pp. 304–305 (PDF pp. 315–316).
