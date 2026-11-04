# Proof of the actual coefficient-matrix unipotence criterion

Authors: Worker 572 (Lean proof and first Markdown draft); Worker 1512
(Markdown revision and submission).

The theorem
`Langlands.GroupScheme.UnipotentMatrixCriterion.corepresentedMatrixUnipotence.{u}`
has type exactly the published statement
`Langlands.GroupScheme.UnipotentMatrixCriterion.CorepresentedMatrixUnipotenceStatement.{u}`
from `Langlands.GroupScheme.UnipotentMatrixCriterion.Statement`, for an arbitrary
universe `u`. It adds no hypotheses. The module imports that statement and the
published coordinate adapter `Langlands.GroupScheme.UnipotentMatrixCriterion.Coordinates`,
and changes neither.

Fix a field `k`, a group-valued functor `F`, an algebra `B` and a
corepresentation `e`. Equip `B` with the bialgebra
`AffineLinearEmbedding.bialgebra e`, as in the statement.

## Actual unipotence implies the matrix criterion

Assume `IsUnipotent (Corepresented.groupScheme F e)`. Let `N > 0` and let
`a : Matrix (Fin N) (Fin N) B` satisfy `IsCoefficientMatrix a`. Then `Fin N` is
nonempty, since it contains `0`.

1. The two fields of `IsCoefficientMatrix a`, its comultiplication and counit
   identities, are the hypotheses of `Corepresented.LinearEmbedding.toGL`. That
   definition gives a natural homomorphism
   `F ⟶ GeneralLinear.functor (Fin N) (CommRingCat.of k)`.
   `Corepresented.groupSchemeMap e (GeneralLinear.corepresentableBy (Fin N) (CommRingCat.of k))`
   turns it into an actual representation
   `ρ : MatrixRepresentation (Corepresented.groupScheme F e) (Fin N)`.
2. Unipotence, applied at the index type `Fin N`, gives `v ≠ 0` with
   `ρ.IsFixedVector v`.
3. `isFixedVector_iff` rewrites this all-test fixedness as the row equations
   `∑ j, v j • coefficientMatrix e ρ i j = v i • 1`.
   `coefficientMatrix_toGL` identifies `coefficientMatrix e ρ` with `a`. These
   are therefore the required equations for `a`.

## The matrix criterion implies actual unipotence

Assume `IsMatrixUnipotent k B`. Let `n : Type` be finite, with decidable
equality, and nonempty. Let `ρ` be an actual matrix representation indexed by
`n`. Write `f : Fin (Fintype.card n) ≃ n` for the inverse of
`Fintype.equivFin n`. Reindex the universal coefficient matrix as
`a i j = coefficientMatrix e ρ (f i) (f j)`.

1. `a` is a coefficient matrix. Its comultiplication identity follows from
   `coefficientMatrix_comul` after reindexing the inner sum along `f`
   (`Equiv.sum_comp`). Its counit identity follows from
   `coefficientMatrix_counit`, since `f` is injective and so `f i = f j` exactly
   when `i = j`.
2. `Fintype.card n` is positive because `n` is nonempty. The matrix criterion
   therefore gives `v : Fin (Fintype.card n) → k` with `v ≠ 0` and the row
   equations for `a`.
3. Pull `v` back to `w = fun i => v (f.symm i)` on `n`. If `w = 0`, then
   evaluating at `f i` shows `v i = 0` for every `i`, which is impossible. So
   `w ≠ 0`.
4. For `i : n`, the row equation of `a` at `f.symm i`, after simplifying
   `f (f.symm i) = i` and reindexing the sum along `f`, is
   `∑ j, w j • coefficientMatrix e ρ i j = w i • 1`.
   `isFixedVector_iff` turns these equations into `ρ.IsFixedVector w`, that is,
   fixedness on every test scheme over `Spec k`. This is what the unchanged
   `IsUnipotent` predicate requires.

## Scope

The proof uses no coalgebra conilpotence, exhaustion, or quotient theorem. It
uses only the given corepresentation `e` over an arbitrary field. It needs no
finiteness, smoothness, reducedness or characteristic hypothesis. The
compiled theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
