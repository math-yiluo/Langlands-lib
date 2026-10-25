# Every square matrix over a field is conjugate to its transpose

`Langlands.MatrixTransposeConjugateStatement.{uK}` is the following unproved
proposition. This module defines the proposition and supplies no proof.

## Statement

For every field `K : Type uK`, every natural number `n` and every matrix
`x : Matrix (Fin n) (Fin n) K`, there is an invertible matrix
`g : Matrix.GeneralLinearGroup (Fin n) K` such that

`(g : Matrix (Fin n) (Fin n) K) * x * (g⁻¹ : Matrix (Fin n) (Fin n) K) = x.transpose`,

where `g⁻¹` is the inverse in `Matrix.GeneralLinearGroup (Fin n) K`. Here
`x.transpose` is Mathlib's ordinary matrix transpose and both coercions are
the underlying matrices of the units. The field is arbitrary: no
characteristic, completeness or algebraic-closure hypothesis is made, and
`n = 0` is allowed. The conjugating matrix has entries in the same field `K`.

## Provenance

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n,F), where F is a non-Archimedean local field (survey)* (1976),
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

In Section 7.3 (printed pp.57–58) the source verifies condition d) of Theorem
6.13 for the conjugation action of `G = GL(n,F)` on itself and the transpose
`σ`, by the sentence "Transposed matrices are conjugate in G" (printed p.58).
The source gives no proof of this classical fact of linear algebra. The present
proposition states it for square matrices over an arbitrary field, which
includes the invertible matrices over a p-adic field needed in the proof of
`Langlands.GeneralLinearConjugationDistributionTransposeStatement`. Mathlib, at
the pinned commit, contains no rational canonical form and no theorem that a
matrix is similar to its transpose.

## Why the proposition is true

This sketch is a plan for the separate proof, not a claimed Lean theorem. It
suffices to find an invertible symmetric matrix `S` with `S * x = xᵀ * S`, that
is, a nondegenerate symmetric bilinear form on `K^n` for which `x` is
self-adjoint. Then `g = S` works.

Make `K^n` a torsion module over `K[X]` with `X` acting by `x`. By Mathlib's
structure theorem `Module.equiv_directSum_of_isTorsion`, it is a finite direct
sum of cyclic modules `K[X]/(q)`. On `K[X]/(q)` with `deg q = d`, let `φ(r)` be
the coefficient of `X^(d-1)` in the reduced representative of `r`. The form
`(a, b) ↦ φ(a b)` is symmetric, multiplication by `X` is self-adjoint for it,
and its Gram matrix `(φ(X^(i+j)))` in the basis `1, X, …, X^(d-1)` has zeros
for `i + j < d - 1` and ones for `i + j = d - 1`, so it is invertible. The
orthogonal sum of these forms, transported to `K^n`, is the required form, and
its Gram matrix `S` satisfies `S * x = xᵀ * S`.
