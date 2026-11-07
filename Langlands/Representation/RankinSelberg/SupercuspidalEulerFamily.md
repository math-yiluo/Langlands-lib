# Actual Euler data for supercuspidal pairs of arbitrary ranks

This internal construction concerns two original irreducible unitarizable
supercuspidal actions of arbitrary positive ranks, with independent field and
two carrier universes, the canonical p-adic topology, a supplied unitary
additive character, and its actual self-dual Haar measure.

`IsRankContragredient` includes equality of the two ranks and an actual
equivalence from the transported first action to the smooth contragredient of
the second. `SupercuspidalPairEuler` packages finite norm-one Euler data with
the actual residue cardinality, a symmetric pair-polynomial certificate, and
the exact parameter-one test given by this rank-sensitive relation.

The constructor retains `SupercuspidalEqualRankLFactorStatement` as an explicit
premise. In equal rank it uses the exact unitary contragredient twist set and
its certified-polynomial adapter. In either unequal rank order it uses the
published proof of the supercuspidal unequal-rank formula and the empty Euler
set. Supercuspidal genericity is deduced from the proved Kirillov theorem and
Whittaker multiplicity one. Admissibility comes from supercuspidality.

Finally, uniqueness of the symmetric polynomial and the equality of the
complex-power and exponential spectral conventions identify the reciprocal
with the actual evaluation of every certified pair polynomial.

This module composes proved Library facts with the explicitly retained
equal-rank formula. It does not prove that formula, a segment formula, or the
associated-pair induction statement.
