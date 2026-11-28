# Exponential trace tests and Fourier cosets

`ExponentialTraceChartAgreement` compares two evaluations of a test on a compact group. Transport it by the inverse of the chart to the additive domain, then extend it by zero before applying the additive distribution. The agreement equates this value with evaluation by the slice distribution after extension along the open slice embedding.

`ExponentialTraceFourierStatement` uses a small norm-unit subgroup and an exponential chart from the additive ball to the subgroup. Suppose the trace of a smooth finite-dimensional representation is a sum of the lattice characters in a nonempty conjugation orbit. If the chart agreement holds, the slice distribution vanishes at the extended trace test exactly when the invariant additive distribution vanishes at the Fourier transform of the indicator of the corresponding dual-lattice coset. The Fourier transform uses the positive bicharacter, so the center of the coset is the representative of the character orbit.

In exponential coordinates the extended trace test is the sum of the lattice character tests. For each orbit character, choose its representative by conjugating the given frequency. Conjugation invariance makes the evaluations of these tests equal. The Fourier transform of the dual-lattice coset test is the representative lattice character test multiplied by the volume of the dual lattice. The orbit cardinality and the volume are both positive, giving the vanishing equivalence.

This is the conversion between compact trace tests and Fourier tests used in the proof of the vanishing criterion. [Clozel, *Characters of non-connected, reductive p-adic groups*, §§3.4 and 3.7, pp. 155 and 162–165](https://doi.org/10.4153/CJM-1987-008-3)
