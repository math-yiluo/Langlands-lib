# Annihilation of actual derived points in a split torus

Author: Worker 1374.

This internal construction works over an arbitrary field `k : Type u`.
For a commutative group scheme `T`, an actual homomorphism `i : T.toGrp ⟶ G`,
an ambient homomorphism `f : rationalPoints G →* Multiplicative ℝ`, and a
rational point `x` of `T`, the additive map `torusEndRealEvaluation i f x`
sends an actual endomorphism `a : T ⟶ T` to the additive real value of
`f(i(a(x)))`. It composes the published actual point evaluation and
rational-point maps.

Every actual normalizer translate has the same real value as the original
whole point: its ambient image is a conjugate, and the target group is
commutative. When the underlying scheme map of `i` is monomorphic, this
descends on representatives to the actual quotient `relativeWeylGroup i`.
If this quotient has a `Fintype` instance, additivity identifies evaluation
of `relativeWeylTorusNorm i` with its cardinality times the real value of
the original point. The norm takes a product of actual Weyl translates.

The theorem `map_eq_one_of_splitTorus_mem_derived` assumes that `G` is
connected reductive, `T` is split, `i` is monomorphic, the actual relative
Weyl quotient is finite, and every actual relative root admits an actual
relative reflection. Its point hypothesis says that `i(x)` belongs to the
actual algebraic `derivedSubgroup G` rational carrier. The theorem proves
`f(i(x)) = 1` without any topology or open-kernel hypothesis.

The implemented proof applies the published centrality of the torus norm
under the explicit reflection premise. Normality of the actual derived
subgroup implies that the norm of the original whole point still lies in
that subgroup. Hence its ambient image belongs to `centralDerivedPoints G`,
and `centralDerivedPoints_le_ker` makes its real value zero. The cardinality
formula then gives the finite group order times the original real value
equal to zero. A finite group has positive order; cancellation in the real
numbers gives the result.

The wrapper `map_eq_one_of_maximalSplitTorus_mem_derived` uses the published
reductive finiteness theorem for the actual Weyl quotient of a maximal split
torus. It obtains splitness and monomorphism from maximal splitness and
retains the same explicit reflection premise.

The provenance is internal composition of the actual torus norm,
normalizer conjugation, subgroup normality, full central-derived torsion
and actual reductive Weyl finiteness. No new literature assertion is used.
Only membership of the whole point in the actual algebraic derived
subgroup is assumed; no membership of its separate coordinate factors,
abstract commutator equality or rational surjectivity of an isogeny is
used. Reflection existence and reduction of general derived rational
points to this split-torus case remain separate obligations. This module
does not prove the full ambient smooth-real annihilation target.
