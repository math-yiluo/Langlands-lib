# Actual orbit comparison values across source cuts

This internal specialization combines the supplied-measure parabolic orbit
equivalence with the genuine compact stages integrand for normalized induction
of normalized Jacquet modules.

`cutOrbitIntegralValue` evaluates that actual equivalence on the actual target
radical coinvariants at a target Levi element. Its value lies in the existing
nested-intersection coefficient coinvariants. The original positive source
half modulus and the existing Haar-ratio coefficient are retained.

`cutOrbitIntegralValue_mk_integral` identifies this value on each actual compact
representative with the integral of `cutOrbitIntegrand`. It specializes the
supplied-measure evaluation theorem to the normalized Jacquet representation;
the two independently named integrands are definitionally identical.

`cutOrbitIntegralValue_cutMap` proves equality of the actual equivalence values
under the actual coefficient cut map when the orbit functions are pointwise
Jacquet quotient projections. The target measure data are the simultaneous
pushforwards of the source kernel, intersection and quotient measures. The proof chains
the two evaluation formulas with the genuine stages integral square. Finiteness on compact sets comes from the supplied source data.

`correctedOrbitRestriction_comparison_cutMap` specializes this equality to the
actual corrected-support restrictions after their canonical support quotient
projections. The actual cut-map restriction theorem discharges pointwise
compatibility, so this result has no additional compatibility hypothesis on
representatives. The support and lower-support sets retain their stated upward
closure hypotheses, and the permutation retains both its source-support and
source-increasing hypotheses.

These are pointwise equalities for the actual supplied orbit equivalences.
They retain arbitrary primes, supplied topologies, ranks including zero, and
independent field and coefficient universes. They do not identify the entire
graded complex with a Boolean complex or prove lower homology vanishing or
signed effectivity.
