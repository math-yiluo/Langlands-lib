# Weighted measure comparison from fibre bounds

`WeightedFibreComparisonStatement` fixes a continuous log weight ℓ and two measurable regions S₀ and S in the rational-parabolic quotient. Suppose S₀ meets every fibre of the projection to the rational quotient, at most N points of each fibre lie in S, and ℓ(Hₚ(z₀)) − ℓ(Hₚ(z)) ≤ d whenever z₀ in S₀ and z in S lie in the same fibre. The pushforward of the weighted measure on S is at most N exp(2d) times the pushforward of the weighted measure on S₀.

The proof expresses each weighted integral on the rational quotient as an integral over its fundamental domain and a sum over the discrete fibre. For each fibre it chooses a term from S₀. Each term from S is at most exp(2d) times this term. The finite point bound gives the comparison of sums, and integration of indicators gives measure domination.

This implements the weighted norm comparison of Bernstein–Lapid, §7.4, p. 215, under supplied coverage, fibre cardinality, and height displacement bounds.
