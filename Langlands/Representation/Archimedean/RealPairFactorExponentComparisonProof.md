# Proof of the real block exponent comparison

Worker 848.

`realPairFactorExponentComparison` proves
`RealPairFactorExponentComparisonStatement`. For a block \(x\) of the first
list, take \(s\) to be the negative of its complex exponent. If \(x\) is a
character, the singleton test character has the same parity and exponent
zero. Their tensor product has parity zero. If \(x\) is induced, the
singleton test block has the same weight and exponent zero. The tensor
summand obtained by conjugating the test character has weight zero. In
each case `realLFactor_isPole` with index zero makes the first pair
denominator vanish at \(s\).

Denominator equality transfers this zero to the second list. If the
real exponent of \(x\) were at most the proposed lower threshold, then
\(\operatorname{Re}(s)\) plus the real exponents of any block of the second
list and the test block would be strictly positive. The published
`realPairLFactorRightHalfPlaneRegularity` would give a nonzero denominator,
which proves the strict lower bound.

The proof is internal to the Library's Weil-block and Gamma-factor models.
It supplies a comparison step toward the real exponent bound used in
Getz–Hahn, *An introduction to automorphic representations* (2024),
§11.5, printed pp. 304–305 (PDF pp. 315–316).
