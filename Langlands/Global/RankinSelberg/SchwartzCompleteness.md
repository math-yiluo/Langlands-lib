# Completeness of the Schwartz seminorm topology

`tendsto_schwartz_sum` takes a series absolutely summable in every Schwartz seminorm. The series and each of its tails define Schwartz functions by the derivative-series theorem. The seminorm of the difference between the full sum and a partial sum is bounded by the corresponding tail of scalar seminorms. These tails tend to zero, so the partial sums converge in the Schwartz topology.

`schwartzCompleteSpace` uses the countable uniformity of the Schwartz topology. For the controlled sequences in the uniform completeness criterion, the n-th consecutive difference has seminorm less than \(2^{-n}\) for all weights and derivative orders at most n. Each fixed seminorm is summable on the sequence of differences. The partial sums of those differences telescope, so the original sequence converges in the Schwartz space. The domain is a real normed space and the range is a complete real normed space.
