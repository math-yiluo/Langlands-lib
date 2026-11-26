# The expansion in sigma on the actual standard parabolic indices

Arthur's functions `tau`, `tauHat` and `sigma` on the actual cocharacter
space are defined by transport from the root-pairing formulas. This module
expresses the expansions as finite sums over the simple relative roots of
the actual group. The index map bijects subsets of the simple roots with
subsets of the abstract base support. Its inverse maps each indexed root
to its character, and the maps preserve inclusion and the cardinalities
of differences.

`arthurRelative_sigma_eq_sum` evaluates the defining sum for sigma on this
index set. `arthurRelative_tau_mul_tauHat_eq_sum_sigma` uses the abstract
product expansion and the same change of indices. The factors are those
of Arthur 2005, §8, (8.2), printed p. 41 (PDF p. 53). The theorem
`arthurRelative_sigma_eq_zero_or_one` uses the abstract characteristic
function result from Lemma 8.3(a), printed p. 42 (PDF p. 54).

`ArthurRelativeSigmaExpansionStatement` packages these facts for nested
subsets of the simple relative roots. `arthurRelativeSigmaExpansion` obtains
its three conjuncts from the named lemmas.
