# The dual triangular Haar chart

`complexGapDualChart` gives the same positive Haar constant for the determinant-normalized triangular chart and its dual. The dual chart applies inverse transpose and a tail reversal to the retained matrix, followed by a lower rectangle with a zero final row and the inverse transpose of the leading factor.

The proof factors the original chart into the retained matrix, the later upper rectangle and the leading group variable. Inverse transpose sends the upper rectangle to its negative transpose in the lower block. Conjugating by the tail Weyl element reverses the rows and puts the zero row last. Transposition and row reversal preserve the rectangular product measures. Inverse transpose and right Weyl multiplication preserve group Haar, which keeps the normalization constant the same. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.3, change between (10.8) and (10.9)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)

`measurable_dualChart` gives the measurability needed to pull back the Bochner integral.
