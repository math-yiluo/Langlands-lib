# A closed coefficient component in the actual central L2 completion

Author: Worker 386.

`Langlands.SquareIntegrableCoefficientHilbertComponentStatement.{uG,uV}`
is an internal proposition definition. It states that an analytically
square-integrable, algebraically irreducible, unitarizable representation
has an actual closed coefficient realization in the completion of the
central L2 model. This module states the proposition and supplies no proof.

## Inputs

The group `G : Type uG` is a topological group whose compact open
subgroups are cofinal among open subgroups. The explicit condition is
that every open subgroup `K` contains a compact open subgroup `L`.
The algebraic complex carrier `V : Type uV` has an independent universe;
it has no given topology or finite-dimensionality assumption.

The representation `ρ` is algebraically irreducible. The full central
quotient `G / Z(G)` has a Borel measurable structure and a specified Haar
measure `μ` that is also right invariant. These measure assumptions are
explicit. The hypothesis
`hsq : IsSquareIntegrableModCenter ρ μ` includes admissibility and the
square-integrability of every actual smooth-dual coefficient norm on
that quotient. Unitarizability supplies an actual invariant positive
definite Hermitian form. No completed embedding or irreducibility
comparison is an input.

## Exact conclusions

The proposition asserts the existence of an actual unitary scalar
central character `c` and an actual smooth-dual functional `ℓ` with
`ℓ.val ≠ 0`. For these choices, let

```text
σ = Induction.centralL2Representation c.character c.norm_eq_one μ
B = Induction.centralL2Form c.character c.norm_eq_one μ.
```

Both are the existing constructions on actual smooth centrally covariant
functions. The central covariance convention is positive: the underlying
coefficient function is `g ↦ ℓ(ρ(g)v)`. The coefficient itself remains
a function on `G`; the Hermitian product descends to the full central
quotient and is integrated there.

The output includes actual objects `j : ρ.IntertwiningMap σ`,
`b : InvariantPositiveForm ρ`, a complex-linear isometry
`e : b.HilbertCompletion →ₗᵢ[ℂ] B.HilbertCompletion`, and an invariant
subrepresentation `R` of `B.completedRepresentation`. Its clauses state:

1. The underlying function of `j(v)` is exactly the published
   `c.coefficientIntertwiner hsq.1.1 ℓ.val v`. Thus the central L2
   membership belongs to the actual coefficient, for every source vector.
2. The source form is exactly the pullback:
   `b.inner v w = B.inner (j v) (j w)`. It is allowed to differ from
   a form initially supplied by unitarizability.
3. The completed isometry agrees on the dense algebraic carrier:
   `e (b.toHilbert v) = B.toHilbert (j v)`.
4. The completed isometry intertwines the two existing completed
   representations on every completed vector.
5. The actual set-theoretic range of `e` is exactly the underlying set
   of `R`, and that set is closed in `B.HilbertCompletion`.
6. Every orbit of the ambient completed representation is continuous
   for the given group topology.
7. The carrier `R.toSubmodule` is nontrivial. Every subrepresentation
   of the restricted representation `R.toRepresentation` whose
   underlying subspace is closed in the inherited topology is bottom
   or top. This is closed irreducibility, including nontriviality;
   it does not assert algebraic irreducibility of the completed carrier.
8. For every ambient completed vector `y`, membership in `R` together
   with an open stabilizer is equivalent to the existence of `v : V`
   such that `e (b.toHilbert v) = y`.

The last clause uses the existing non-Archimedean `smoothVectors`,
defined by open stabilizers. The image map from `V` is injective because
`toHilbert` is injective and `e` is a linear isometry. Thus this clause
recovers the original algebraic representation as the smooth vectors
of the closed component. Neither completeness nor a dense-image
condition for that component is assumed as a separate certificate.

## Internal provenance and proposed proof boundary

This is a derived application statement formulated from the published
central coefficient functions, central L2 integral form, invariant
positive forms and their actual Hilbert completions. It is not a
transcription of a separately numbered theorem in the literature.
Its imports define the objects in the proposition and do not import
a proof of this component statement.

A subsequent proof can obtain a nonzero smooth-dual functional from an
invariant positive form, restrict its coefficient intertwiner using
the analytic hypothesis, and pull back `B`. Form preservation then
extends that actual map isometrically to the two completions.
Completeness of the source completion gives closedness of its range.
Admissible smooth-vector recovery and the algebraic-to-closed
irreducibility comparison give the remaining component conclusions.
Continuity of ambient orbits follows from the smoothness of the
central L2 carrier and the isometric completion action.
These sentences describe a proposed route, not an implemented proof
or additional hypotheses of the proposition.

This statement supplies no mirabolic restriction, quotient-measure
transport, Fourier transform, Mackey decomposition, or nonzero
Whittaker functional. Those remain separate obligations of the
intrinsic genericity argument.
