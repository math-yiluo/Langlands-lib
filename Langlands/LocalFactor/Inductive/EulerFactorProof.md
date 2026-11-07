# Inductivity of the Euler factor of actual local Weil representations

`Langlands.LocalFactor.Inductive.eulerFactorInduction` proves the existing
`EulerFactorInductionStatement.{u}` for every prime `p`, with its original
universe and all its hypotheses. It retains arbitrary p-adic fields, the
actual map `extensionWeilMap`, the actual representation `induceAlong`,
and arbitrary degree-one geometric Frobenius elements in both fields.

The proof compares the actual induced inertia-invariant space with the
degree-kernel invariants of Mathlib's coinduction along the original Weil map.
`InductionAlong.invariantCoinductionEquiv` preserves every function value and
intertwines every ambient group element. Its conjugation therefore identifies
the actual induced Frobenius operator with the coinduced invariant action.
The proof composes this equivalence with the degree coordinates before
comparing Euler polynomials.

The positive residue degree is written `n + 1`. The published local degree
scaling identity supplies the hypotheses for `InductionDegree.coordinates`.
In these coordinates, `cyclicOperator_zero` and `cyclicOperator_succ` identify
the transported Frobenius action: coordinate zero is the source Frobenius
applied to the last coordinate, and each successor coordinate is the preceding
coordinate.

Applying `eulerCyclicBlock` to this operator gives the source Euler polynomial
with `X` replaced by `X^(n+1)`. Invariance of `eulerPolynomial` under linear
conjugation removes both coordinate changes. `Polynomial.expand_eq_comp_X_pow`
expresses the result as expansion by the actual residue degree.

Finally, `extensionExpandedPolynomial_eval` uses the actual relation
`q_E' = q_E^f` to identify evaluation at `exp(-s * log q_E)` with evaluation
of the source polynomial at `exp(-s * log q_E')`, for every complex `s`.
This proves both conjuncts of the original statement. The algebraic proof
does not need the supplied continuity hypothesis, which remains in the exact
target and is not replaced by any additional assumption.

This is an internal proof of the already published Library statement in
`Langlands.LocalFactor.Inductive.Statement`. Its implementation uses the
separate coordinate, local comparison, and cyclic determinant constructions
described above. It makes no new claim about the target documentation's
literature attribution. The target pair and every pair it imports are
preserved.
