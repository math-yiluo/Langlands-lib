# The normalized ordinary integral on the retained chart

`complexGapRetainedMellin` concerns the ordinary complex integral with rank difference at least two. It uses the supplied compatible smaller quotient measure and opposite Whittaker trace scales. The larger coefficient is the continued Godement integral of a split Schwartz test at Godement parameter zero, right translated by the tail Weyl element.

The supplied family `J(p,s)` is continuous in the retained point `p` for each spectral value `s`. For each `p`, it is entire with exponential growth on vertical strips. On a right half-plane that may depend on `p`, the normalized ordinary fiber equals `J(p,s)` whenever its kernel is integrable. On the same half-plane the normalized reflected fiber equals `E(1−s) J(p,1−s)` whenever the reflected kernel is integrable. Here `E` is the product of the lower-rank and square reflection factors.

The integral of `J` against the tail test and adjoining determinant character is absolutely convergent at every spectral point and is entire. On a right half-plane, the ordinary integral multiplied by its pair denominator equals this retained integral times the ordinary Weyl phase and a positive Haar scalar. For fixed ranks and trace scale the scalar is common to all split tests.

The proof separates the leading Haar factor from the retained coordinates on both sides. The reflected side also moves the lower rectangle into the lower unequal-rank measure and reindexes its rows. The two reindexed kernels have the absolute moments of the original charts. `archimedeanMellinMarginal` integrates the entire retained family using these moments and the two fiber identities. The exact ordinary restriction compares the result with the original normalized integral on a right half-plane.

The chart and ordinary and reflected separations implement the product structure in [Jacquet, *Archimedean Rankin–Selberg Integrals*, §10.4](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
