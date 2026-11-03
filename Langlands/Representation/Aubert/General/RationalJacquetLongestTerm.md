# Longest-representative specialization of the actual common Jacquet term

`rationalLongestJacquetTerm` restricts the actual common term to the longest
representative, labeled by the literal finite subsets of the associated Levi.

This internal adapter evaluates the actual rational common term at the specified
longest representative and identifies it with the literal transported
associated-Levi term. Field and representation universes are independent.

The proof supplies support from the right ascents of the longest representative.
The associated finite-subset equivalence identifies the target label, and the
inverse simple-image intersection identity identifies the source label. Actual
associated coarse and descendant Levi conjugation and restricted parabolic and
unipotent membership use the same normalizer lift. The actual standard Haar
factorization follows from continuity of standard projections. Jacquet
restriction in stages and the proved induction transport then identify the
whole term with its literal transported associated-Levi expression.

All structural hypotheses are those of the rational target: point Coxeter
comparisons, standard cocharacters and Levi intersection/conjugation, closed
standard Levis and radicals, finite-length and exactness preservation, continuous
standard projections and compact-limit restricted radicals. No extra character,
representation or K0 comparison is assumed. This adapter leaves geometric
expansion and the general minimum-representative term reduction open.

`rationalJacquetLongestTermReduction` supplies the exact survivor comparison
used by `jacquetCompatibility_of_geometricExpansion`. The section of the
normalizer quotient must take the chosen longest representative to the specified
normalizer element. Substituting that equality retains the same actual element
in every conjugation and uses proof irrelevance only for membership witnesses.

A private index-transfer lemma first substitutes the finite label equalities
before evaluating the supported common term. This keeps the dependent
subgroup maps aligned without simplifying their representation constructions.
