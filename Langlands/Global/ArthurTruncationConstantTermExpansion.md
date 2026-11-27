# The full constant term of the truncation sum

Finite subsets of the simple-root subtype correspond to the subsets of the defining simple character finset. The map forgets the root-membership proof and preserves cardinalities. `truncation_eq_sum_cutoffSeries` uses that correspondence to reindex Arthur's finite parabolic sum and its signs.

The absolute majorant on a full radical orbit bounds each rational-coset series there. Measurability of the series follows from measurability of the kernels, and its invariance descends it to the compact testing quotient. These facts give integrability for each parabolic contribution. `constantTerm_truncation_eq_bruhat` applies finite-sum linearity of the integral and then the single-kernel Bruhat expansion. This is the passage from individual kernel series to the full constant term in the proof of Arthur (1980), Lemma 1.1.
