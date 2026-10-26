# Polynomial-module isomorphisms give matrix conjugacy

`Langlands.MatrixAEvalConjugacyStatement.{uK}` is an unproved proposition.
This module states it and supplies no proof.

For every field `K : Type uK`, natural number `n`, and two matrices `x` and
`y` in `Matrix (Fin n) (Fin n) K`, every `Polynomial K`-linear equivalence
between `Module.AEval' x.mulVecLin` and `Module.AEval' y.mulVecLin` implies
that there is `g : Matrix.GeneralLinearGroup (Fin n) K` with
`(g : Matrix (Fin n) (Fin n) K) * x * (g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) = y`.
The inverse in this formula is the inverse in the general linear group,
coerced to a matrix. Neither `x` nor `y` is assumed invertible. The statement
allows `n = 0`, arbitrary characteristic and arbitrary fields.

The underlying vector space of `Module.AEval' x.mulVecLin` is `Fin n → K`.
The action of the polynomial variable `X` is matrix multiplication by `x`.
A polynomial-linear equivalence therefore restricts to a `K`-linear
equivalence intertwining `x` and `y`. Its matrix `g` satisfies `g * x = y * g`,
which gives the displayed conjugation formula. This paragraph explains the
intended mathematical argument; its formal proof is a separate contribution.

## Provenance

This is an internal linear algebra bridge for the matrix transpose-conjugacy
and fixed-characteristic-polynomial finiteness proofs. It is not a quotation
or reformulation of a separate source statement. The formulation uses
Mathlib's existing `Module.AEval'`, `Matrix.mulVecLin` and
`Matrix.GeneralLinearGroup` constructions, without adding data or hypotheses.
