# Complex ordinary Rankin–Selberg normalized generation

`complexOrdinaryNormalizedGeneration` proves `ComplexOrdinaryNormalizedGenerationStatement`. For the supplied irreducible inducing lists, opposite nonzero trace scales and compatible quotient measures, every complex spectral point has a nonzero ordinary normalized value. In equal and adjacent ranks at either standard sign, a finite sum of ordinary normalized values is identically one.

`complexOrdinaryEqualAdjacentGeneration` supplies the finite identities at standard scale. Its proof establishes pointwise covering by polynomial normalized tests, using the normalized square convolution span and the alternating equal and adjacent Godement trace identities. Polynomial Bézout then gives a finite unit sum, with each polynomial multiple realized by ordinary normalized tests. The adjacent identities also start the induction on the difference of the ranks.

For a larger rank difference, the proof removes the first entry of the larger inducing list. Irreducibility at the retained rank follows from the sublist criterion. The induction hypothesis supplies covering for that retained pair. `complexOrdinaryGapCoverage` lifts it to the full larger list. This step chooses a leading square convolution with a nonzero retained normalization at the prescribed point and then uses Gaussian moments on the retained tail to obtain a nonzero ordinary pairing. The split Godement test belongs to the compact-finite model, and the entire retained Mellin identity identifies the resulting normalized value.

`complexOrdinaryStandardGenerationReduction` transfers the standard-scale conclusions to the supplied trace scales. The finite sums transfer at both standard signs, with the quotient-measure change included in the reduction.

The generation conclusions are from Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Remark 2.2 and Theorems 2.3, 2.6 and 2.7, author-posted pp. 7–10. Sections 8–10 give the square and rectangular integral identities underlying the rank steps. [Author-posted paper](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
