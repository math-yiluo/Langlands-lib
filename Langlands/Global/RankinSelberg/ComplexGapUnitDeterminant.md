# The triangular chart with retained determinant of absolute value one

`complexGapUnitDeterminant` expresses complex Haar measure in the triangular chart with a retained matrix whose normalized determinant has absolute value one. The leading block is multiplied by the positive scalar whose logarithm is minus the sum of the tail logarithms divided by the leading size. The outer measure acquires the inverse tail determinant to the power `q`, the number of later rectangular columns.

The proof compensates for the scalar in the leading Haar variable and the later rectangular entries. Conjugation by the leading scalar rescales the later rectangle and fixes the unipotent tail. Translation leaves the leading Haar measure invariant. The additive determinant formula supplies the later rectangle Jacobian, and Fubini moves it to the measure on the logarithmic tail. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, determinant-one coordinates, pp. 73–74](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)

`measurable_normalizationWeight` gives measurability of the normalization density on the log-diagonal factor.

`continuous_unitRetained` records continuity of the retained matrix in the outer coordinates.
