# The normalized ordinary integral on the retained chart

`complexGapRetainedMellin` expresses the entire ordinary normalized integral as the integral of the retained family times the tail test and adjoining character. Its scalar is the product of the exact restriction's positive Haar constant and the ordinary Weyl phase. The positive Haar constant depends on the chart measure and additive scale. It is common to all split tests.

The proof separates the leading Haar factor from the retained coordinates on both sides. The reflected side also moves the lower rectangle into the lower unequal-rank measure and reindexes its rows. The two reindexed kernels have the absolute moments of the original charts. `archimedeanMellinMarginal` integrates the entire retained family using these moments and the two fiber identities. The exact ordinary restriction compares the result with the original normalized integral on a right half-plane.

The chart and ordinary and reflected separations implement the product structure in [Jacquet, *Archimedean Rankin–Selberg Integrals*, §10.4](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
