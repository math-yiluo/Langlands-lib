# Twisted pseudo-coefficients from spectral splitting and trace Paley–Wiener

`TwistedPseudoCoefficientSeparationReductionStatement` has two premises,
`TwistedTracePaleyWienerStatement` and
`TwistedPseudoCoefficientSpectrumSplittingStatement`. Its conclusion is
`TwistedPseudoCoefficientExistenceStatement` with all three universe levels
free. `twistedPseudoCoefficientExistence_of_spectrumSplitting` proves the
implication.

The rank reduction supplies ranks zero and one. In rank at least two, use the
spectral splitting to construct the compactly dominated, regular functional
with the prescribed twisted character values at the given central character.
Apply the good-to-trace direction of twisted trace Paley–Wiener with the given
Haar measure. The resulting compactly supported test function realizes the
functional on every admissible irreducible twisted pair. Its traces therefore
satisfy the normalization and vanishing conditions in
`IsTwistedPseudoCoefficient`.

This is the realization step in Henniart–Lemaire (2011), II.5.13, printed
p. 114, using II.5.7, p. 105. The Library's conclusion uses the function on
`GL_n(E)` returned by Paley–Wiener. The spectral evaluations in the proof
use the same measure and central character as the target.
