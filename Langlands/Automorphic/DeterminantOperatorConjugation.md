# Actual determinant conjugation of the concrete automorphic operator algebra

Author: Worker 2. This internal construction uses the actual finite-smooth
complex rational-invariant functions for every number field `F : Type u`
and natural rank, including zero.

`finiteSmoothDeterminantConjugation` is the algebra automorphism of their
endomorphisms sending `A` to `Mχ⁻¹ A Mχ`, where `Mχ` is actual finite-order
determinant multiplication. The finite and compact generator formulas scale
the original right translation by the corresponding value of `χ(det g)`.
The differential generator formula fixes every element of the genuine
enveloping action. These formulas follow from actual covariance and whole
enveloping commutation, followed by inverse cancellation.

Induction over the published generated subalgebra proves that conjugation
preserves the existing `automorphicOperatorAlgebra`. Scalar multiples of
each finite or compact generator remain in that subalgebra, and every
differential generator is fixed. Algebra scalar, sum, and product closure
handle the induction. The inverse character gives the inverse conjugation
and preserves the same algebra.

`determinantOperatorConjugation` is consequently an actual algebra
automorphism of this concrete operator algebra. It inherits the existing
operator identities; no free algebra or independently supplied action is
substituted. Its underlying ambient operator is identified exactly.
`operatorAction_determinantMultiplier` states the whole-algebra identity
`A Mχ f = Mχ (conjugationχ(A) f)` on actual finite-smooth functions.

The provenance is direct internal application of Mathlib's linear-equivalence
conjugation construction and generated-subalgebra induction to
`DifferentialDeterminantMultiplier` and `OperatorCore`. No continuity of
the operator-algebra automorphism, preservation of all automorphic forms,
nonzero invariant core, or total twist of a realization is asserted here.
