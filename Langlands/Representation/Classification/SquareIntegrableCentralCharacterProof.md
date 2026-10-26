# Elementary central-character reductions for square-integrability

Worker 19 implements `Langlands.glSquareIntegrableCentralCharacter`, with exact
type `Langlands.GLSquareIntegrableCentralCharacterStatement.{uF,uV}`.
Worker 349 is a coauthor: the open-kernel helper and scalar-centre construction
are adapted from his private helpers in `TemperedExponentEdgeProof`.

This auxiliary proves the published central-character reductions. It does not
prove the strict Jacquet-exponent criterion.

## Implemented proof

The generic private helper `scalarCharacter_open_kernel` chooses a nonzero
vector and a smooth open subgroup fixing it. Its inverse image under the
continuous group homomorphism is open and lies in the scalar character's kernel,
by cancellation of scalar multiplication on that vector. A subgroup containing
an open subgroup is open.

The helper `scalarCharacter_norm_eq_one` compares the prescribed scalar action
with the action of a supplied `UnitaryCentralCharacter`. Cancellation on a
nonzero vector identifies their complex values at each scalar matrix; the unit
norm property follows from that of the centre character.

The helper `exists_unitaryCentralCharacter` uses positive rank to make
`GeneralLinear.scalarToCenter` injective. Mathlib's
`Matrix.GeneralLinearGroup.center_eq_range_scalar` gives surjectivity. The
resulting multiplicative equivalence transports `ω` to the actual centre. The
norm-one and scalar-action fields follow by construction; open kernel follows
from the generic helper applied to inclusion of the centre. This avoids any
need to assert continuity of the inverse centre parametrization.

The public theorem assembles the four clauses:

1. Apply the open-kernel helper to the continuous scalar embedding.
2. Combine the comparison and construction helpers for the equivalence.
3. Choose a Haar measure using `T.exists_isHaarMeasure_centralQuotient`,
   extract a unitary centre character from square-integrability for that
   measure, and compare its action with `ω`.
4. For each Haar measure, replace its existential central-character witness by
   the fixed witness using `UnitaryCentralCharacter.coefficientNorm_eq`.
   Conversely, the fixed witness and the assumed admissibility give the
   analytic predicate for each measure directly.

All vector and field universes remain independent. The proof uses no
irreducibility, finite length, finite-dimensionality or spectral assumption.
It establishes no estimate on coefficients. In particular the final clause
retains every Haar measure and is not a one-measure normalization theorem.

## Dependency audit

The only direct import is the target statement, whose direct import is
`Langlands.Representation.Classification.Tempered`. The proof uses the existing
definitions of admissibility, smoothness, unitary centre character, descended
coefficient norms and square-integrability; the established existence of Haar
measure; the scalar embedding and its continuity; and Mathlib's algebraic
description of the matrix-group centre and elementary scalar cancellation.

The copied helper route is reproduced explicitly and does not import
`TemperedExponentEdgeProof` or invoke its weak-exponent theorem. No strict or
tempered exponent criterion, segment analytic classification, multisegment
special-head exhaustion, ordered special-head existence, quotient coverage,
tempered block uniqueness, square-integrable Langlands classification,
square-integrable exhaustion or regular exhaustion theorem is used. This
elementary unit has no dependency on the pending analytic tasks of the parent
criterion.
