# Uniform torsion in the full central derived intersection

Author: Worker 1374.

This internal helper combines published Library theorems. It defines
`Langlands.BruhatTits.RationalPoints.centralDerivedPoints G` as the intersection
of the rational carriers of `center G` and `derivedSubgroup G`. Here `center`
is the scheme-theoretic centre, tested after every restriction of the test
scheme. The definition is available over any commutative ring. It does not
replace the algebraic derived subgroup by abstract group commutators.

For a connected reductive group scheme `G` over an arbitrary field `K : Type u`,
`IsConnectedReductive.exists_pow_eq_one_of_mem_center_derived` proves that
there is one positive natural number `N` such that `x ^ N = 1` for every
test scheme `T` over `Spec K` and every `T`-point `x` in both subgroup
functors. The bound applies to nonreduced test schemes as well.

The implemented proof first chooses an actual closed derived inclusion
`d : D ⟶ G` using `derivedSubgroupRepresentability`. The theorem
`derivedCentralIntersectionFiniteness` then provides a finite closed
`c : C ⟶ D` with full range equal to `(center G).comap d`. Thus the
composite `c ≫ d` is central and monomorphic. Its source is commutative by
`IsCentral.isCommMonObj`. The published theorem
`exists_pow_eq_one_of_isFinite C` supplies a positive exponent for every
point of this finite commutative group scheme. Each point in the central
derived intersection lifts first through `d`, then through `c`, by their
full range equalities. Transporting the exponent equality through the two
group homomorphisms proves the assertion.

`exists_pow_eq_one_centralDerivedPoints` specializes the same bound to
rational points. `centralDerivedPoints_le_ker` proves that every group
homomorphism `f : rationalPoints G →* Multiplicative ℝ` kills this subgroup.
Applying `f` to the power equality and writing the result additively gives
`N * (f x).toAdd = 0`; positivity of `N` forces `(f x).toAdd = 0`.
The theorem uses no openness, continuity, local-field, splitting,
perfectness or characteristic hypothesis.

Finally, `map_eq_one_of_isCentral_range_le_derived` applies that kernel
inclusion to the rational images of any actual central homomorphism whose
full range lies in `derivedSubgroup G`.

The provenance is the above internal composition of published results,
without a new literature assertion. It does not prove that all derived
rational points are central, or complete the ambient smooth-real
annihilation target. Structural arguments reducing general derived
points to these cases remain separate obligations.
