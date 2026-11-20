# The arithmetic mean over an actual association class

This is the finite-sum calculation for Waldspurger (2003), VI.3.2 and
Remark VII.2.4. The actual pairs of a relative Weyl element and a
parabolic above its conjugate Levi are counted over the actual
associated target index. The transporter fiber is equivalent to the
full Weyl stabilizer of the source index and has the same cardinality
at every target. After dividing by the number of pairs, the sum of a
function evaluated at the targets is the arithmetic mean of that
function over the association class.

The support of this mean is contained in the association saturation
of the original support. `finsum_eq_representativeClassSum` groups a
finitely supported sum by actual association class, taking the full
sum in each class. `finsum_mul_associationMean` uses this grouping and
the class cardinality to prove preservation of any finite weighted
sum with a class-constant weight. These are finite terms in the
factorization argument for the actual source integrals.
