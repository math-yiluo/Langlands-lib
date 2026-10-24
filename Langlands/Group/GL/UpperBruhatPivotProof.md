# Ordered pivot isolation for upper Bruhat induction

Authors: Worker 330 (Lean proof and documentation) and Worker 308
(pivot-isolation interface and proof design).

`Langlands.GeneralLinear.fieldUpperBruhatPivotTheorem.{u}` proves the closed
published proposition `Langlands.GeneralLinear.FieldUpperBruhatPivotTheorem.{u}`.
It retains every field `K : Type u`, every natural `n`, and every
`g : Langlands.GeneralLinear (n + 1) K`. No pivot, elimination certificate,
minor-invertibility assumption, or Bruhat factorization is supplied by the caller.
The existing statement pair and its imports are unchanged.

## Implemented proof

Write `last = Fin.last n` and let `r j = g last j`. The identity
`g.val * g.inv = 1`, evaluated at `(last, last)`, proves that `r` is not
identically zero. The proof chooses `p` as the least element of the finite set
of columns where `r` is nonzero. Thus `a = r p` is nonzero and `r j = 0` for
`j < p`.

Define the row correction coefficients by

- `c p = a⁻¹ - 1`;
- `c j = -(a⁻¹ * r j)` when `j ≠ p`.

The right correction matrix is `Rm = I + E`, where `E i j = c j` if `i = p`
and `E i j = 0` otherwise. The private lemma `pivot_mul_row` expands right
multiplication as `(A * Rm) i j = A i j + A i p * c j`.
Minimality of `p` proves that `Rm` is upper triangular. Its diagonal is `a⁻¹`
at `p` and one elsewhere, so Mathlib's triangular determinant formula makes
its determinant nonzero. `Matrix.GeneralLinearGroup.mkOfDetNeZero` supplies
an actual matrix unit `R` with this value. Applying the multiplication formula
shows that `q = g * R` has last row equal to the unit row supported at `p`.

For the left correction, let `d last = 0` and `d i = -q i p` otherwise.
Set `Lm = I + F`, where `F i j = d i` when `j = last`, and zero otherwise.
The private lemma `pivot_col_mul` expands left multiplication as
`(Lm * A) i j = A i j + d i * A last j`. The correction is upper triangular
because its only possibly nonzero extra column is the last one; every diagonal
entry is one. The same determinant argument produces an actual unit `L`.
The multiplication formula proves that `A = L * g * R` preserves the normalized
last row and has `A i.castSucc p = 0` for every `i : Fin n`.

The private lemma `pivot_minor_unit` then constructs both matrices

- `B i j = A i.castSucc (p.succAbove j)`;
- `C i j = A.inv (p.succAbove i) j.castSucc`.

To prove `B * C = I`, it evaluates `A.val * A.inv = I` at the two `castSucc`
indices and splits the sum into column `p` and the remaining columns using
`Fin.sum_univ_succAbove`. The isolated pivot column makes the omitted summand
zero. To prove `C * B = I`, it evaluates `A.inv * A.val = I` at the two
`p.succAbove` indices and splits the sum into the first `n` rows and the last
row using `Fin.sum_univ_castSucc`. The last-row summand vanishes because
`p.succAbove j ≠ p`; injectivity of `p.succAbove` identifies the identity
matrix entries. These two identities directly construct the matrix unit `h`
with value `B` and inverse `C`.

The resulting `L`, `R`, `p`, and `h` satisfy all five published conjuncts.
The columns of the minor are exactly the increasing enumeration `p.succAbove`,
with no alternate ordering. For `n = 0`, the minor and its inverse are empty
matrices, and the same two inverse proofs apply; the remaining scalar pivot
is still normalized to one.

## Provenance and scope

This is internal algebraic proof infrastructure for the project's upper Bruhat
induction. The construction implements Worker 308's proposed least-pivot and
complementary-inverse route using existing Mathlib matrix and finite-sum
identities. It claims no external literature theorem. The theorem proves only
pivot isolation; the parent's induction and final factorization remain separate.
