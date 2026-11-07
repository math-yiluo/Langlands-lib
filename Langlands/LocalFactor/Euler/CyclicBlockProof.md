# Cyclic block identity for determinant Euler polynomials

Worker 1820 proves the published proposition
`Langlands.LocalFactor.EulerCyclicBlockStatement.{u,v}` as
`Langlands.LocalFactor.eulerCyclicBlock`, in the module
`Langlands.LocalFactor.Euler.CyclicBlockProof`.

For an arbitrary field `K`, a finite-dimensional `K`-vector space `V`, and
`A : Module.End K V`, let `T` act on `Fin (n+1) → V` with
`T v 0 = A (v (Fin.last n))` and `T v i.succ = v i.castSucc`.
The theorem proves all three conjuncts of the existing statement: the
polynomial identity `P_T(X) = P_A(X^(n+1))`, its evaluation at every `x : K`,
and the equality of the existing regular reciprocal values at `x` and
`x^(n+1)` when supplied with the statement's nonvanishing witnesses.
The field and carrier universes are independent. There are no extra
hypotheses on the characteristic, on `A`, on `n`, or on the dimension.

## Implemented determinant argument

The helper `CyclicBlock.pencil A n a b`, for a finite square matrix `A` over
any commutative ring, is indexed by `Fin (n+1) × ι`. It is the identity,
minus a wraparound block `a A` in position `(0,n)`, minus the subdiagonal
blocks `b I`. This definition also covers `n=0`: the wraparound shares the
single diagonal block and the subdiagonal term vanishes.

`CyclicBlock.det_pencil` proves

```
det (pencil A n a b) = det (1 - (a * b^n) • A).
```

The base case reindexes `Fin 1 × ι` by `ι`. For the induction step, the
private equivalence `headEquiv` separates the first block, giving a matrix
`fromBlocks 1 B C D`. Mathlib's `Matrix.det_fromBlocks_one₁₁` identifies its
determinant with `det (D - C*B)`. Entrywise multiplication shows that `C*B`
is supported only in the new wraparound position and contributes
`(a*b) A`. Thus the Schur complement is `pencil A n (a*b) b`.
Induction gives the displayed formula. All of this takes place over a
commutative ring, without division or a nonempty index assumption.

For the vector-space identity, `eulerPolynomial_cyclicBlock` chooses
`Module.finBasis K V` and the induced product basis, reindexed by
`Fin (n+1) × Fin (Module.finrank K V)`. The two supplied coordinate formulas
for `T` identify its matrix with the cyclic shift and wraparound blocks.
Over `K[X]`, the matrix defining its Euler polynomial is therefore the
pencil with `a=b=X`. The determinant lemma yields
`det (1 - X^(n+1) • A_matrix)`. The private lemma
`eulerPolynomial_comp_eq_det` identifies this with
`(eulerPolynomial A).comp (X^(n+1))`: polynomial composition is a ring
homomorphism, so it commutes with determinants. The existing
`eulerPolynomial_eq_det` supplies both determinant descriptions.

Finally, `eulerCyclicBlock` evaluates the polynomial equality using
`Polynomial.eval_comp`. It proves the regular-value equality by unit
extensionality: the underlying scalar of each regular reciprocal value is
the inverse of the corresponding polynomial evaluation. The evaluation
identity equates these inverses. The nonvanishing witnesses remain exactly
the ones required by the published statement.

The argument includes `n=0` through the determinant base case. When `V` has
dimension zero, the chosen basis index is empty; the determinant lemmas
and basis constructions still apply, so no separate positive-dimension
premise is introduced.

## Provenance and dependencies

This is an internal algebraic proof of the existing Library target in
[`Langlands.LocalFactor.Euler.Statement`](Statement.md), using the actual
Euler polynomial and regular values in
[`Langlands.LocalFactor.Euler.Definitions`](Definitions.md). Its mathematical
provenance is the published target; the pencil and elimination argument
above are auxiliary constructions for this proof. No new source translation
or independent verification of the target documentation's literature
attribution is claimed. The proof route uses Mathlib's Schur-complement,
finite-basis, matrix-determinant, and polynomial-composition APIs.

The target pair and its imported project pair are unchanged. This module
supplies the generic linear-algebra prerequisite; applications to Weil
groups and inertia invariants use their separately constructed operators.

## Development validation

The proof compiled without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). Theorem inspection reports
universe parameters `u,v` and only `propext`, `Classical.choice`, and
`Quot.sound`. These are development checks; independent semantic review,
exact-target validation, and publication are supplied by the submission
workflow.
