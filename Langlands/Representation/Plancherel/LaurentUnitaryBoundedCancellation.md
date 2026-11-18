# Cancellation of coordinate poles from dense unitary bounds

This derived unit isolates the elementary boundedness-to-divisibility step
used in Waldspurger (2003), V.2.3, printed p.294 / PDF p.60, and reused in
Lemma V.3.1, printed p.295 / PDF p.61. It imports the coordinate divisibility
unit `LaurentUnitaryHyperplaneDivisibility`. The registered original is
`waldspurger-2003-plancherel`. These lemmas concern finite Laurent polynomials,
not an assertion that a given standard intertwiner has the required pole
support or norm identities.

`finiteLaurentUnitaryEvaluation n` constructs the restriction algebra
homomorphism from the finite Laurent algebra to scalar functions on the
unitary torus. `finiteLaurentUnitaryEvaluation_apply` identifies its values
with the existing finite Laurent evaluation.
`continuous_finiteLaurentUnitaryEvaluation` proves continuity of each
constructed restriction.

The imported `continuous_finiteLaurentEvaluation_circle` proves continuity of every finite
Laurent polynomial evaluated on the full unitary torus. Its proof uses the
finite sum of Laurent monomials and continuity of integral powers on the circle.

`norm_eq_zero_of_dense_norm_le` treats a continuous function into a seminormed
additive group and a continuous scalar denominator on an arbitrary topological
space. If the numerator seminorm is at most a fixed real constant times the
denominator norm on a dense subset, its seminorm is zero at each denominator
zero. The proof extends the inequality using a closed sublevel set. For a
seminormed group the conclusion is only a zero seminorm.

`finiteLaurentCoordinateRoot_dvd_of_dense_unitary_bound` treats a complex
Laurent numerator `p`, a Laurent denominator `b`, a dense set of points in the
entire unitary torus, a point `a` on the circle, and a fixed real bound for the
cleared numerator inequality. If `X₀ - a` divides `b`, the theorem concludes
that the same factor divides `p`. It does not assign any value to a quotient
at a pole and assumes no extension on an ambient complex open set.

The denominator restriction to the coordinate slice is zero by its factor
divisibility. The continuous numerator inequality then forces the numerator
to vanish on that entire unitary slice. The imported Laurent coordinate
divisibility theorem gives algebraic divisibility.

Known root-pole support for the actual tensor, actual root-coordinate changes,
iteration for pole multiplicities, one common denominator for all operator
vectors, and the construction of the actual all-unitary family remain separate
obligations.
