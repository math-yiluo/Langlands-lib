# Joint continuity of locally holomorphic finite Eisenstein families

`FiniteMeromorphicFamilyJointContinuityStatement` concerns a scalar-valued family
on a complex parameter space and a topological space. At each point of the
topological space, the family is meromorphic with holomorphy domain `O`. On a
nonempty open parameter patch, it agrees on the common holomorphy domain with
a finite entire-weighted sum of meromorphic families. The summands may have
different holomorphy domains. If each summand admits a jointly continuous cleared
numerator near each parameter in `O`, the combined family is jointly continuous
in linear coordinates on `O` times the topological space. The clearing factors
are products of nonzero complex-linear forms centred at the given parameter.

`finiteMeromorphicFamilyJointContinuity` first uses
`eqOn_meromorphic_sum_of_eqOn_open` for each fixed topological variable. The
finite intersection of the summands' domains is open and dense in coordinates,
and the scalar meromorphic identity theorem extends the agreement to its
intersection with `O`.

`continuousOn_of_sum_rootHyperplane_cleared` then takes the union of the
individual clearing sets and the maximum of their exponents. Each cleared
numerator is multiplied by the missing factors and by its scalar coefficient.
The sum of the resulting numerators is continuous on the common neighbourhood
times the topological space. For each fixed topological variable, continuity
extends the cleared identity from the dense intersection to its holomorphy
domain. The transverse-circle argument of
`continuousAt_of_rootHyperplane_cleared` recovers joint continuity at the
centre of the neighbourhood.

Bernstein and Lapid's Theorem 2.3(6) and the Corollary in §8.6 give the
root-hyperplane form for an individual Eisenstein series. The common clearing
argument is the finite-family consequence used with the working hypothesis
and the wave packet proof in Lapid's paper.

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), Theorem 2.3(6), p. 191 (PDF p. 5),
  and §8.6, Corollary, p. 226 (PDF p. 40).
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`
  (SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), §2, p. 312 (volume PDF
  p. 321), and §8, p. 328 (volume PDF p. 337).
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`
  (SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`).
