# Hermite reduction of integral positive definite forms

Author: Worker 19.

This module proves two facts about a symmetric bilinear form `β` with values
in `ℤ` on a free `ℤ`-module `L` of rank `d` (a "lattice"), when `β` is
positive definite:

1. **Hermite's inequality.** If `a` is the least value `β(x,x)` over
   nonzero `x`, then `3^(d choose 2) · a^d ≤ 4^(d choose 2) · det β`.
2. **Reduction.** For each `d` and each bound `Δ` there is a constant `C`
   such that, whenever `det β ≤ Δ`, the lattice `L` has a basis whose Gram
   matrix has all entries of absolute value at most `C`.

Here `det β` is the determinant of the Gram matrix in any basis. Over `ℤ`
it does not depend on the basis (`det_toMatrix_eq`).

The second fact is the step of the finiteness argument for class numbers
in which the positive definite forms of bounded determinant are reduced to
finitely many Gram matrices. The module is a prerequisite for the
finiteness of `GJ(ℚ)\GJ(𝔸_f)/K` for a definite unitary group, which Harris
(1999), §4, uses throughout. It does not depend on any Langlands module.

## Source

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
Theorem 4.18 (ii), printed p. 229 (PDF p. 239): "(Hermite). If `F` is a
positive definite form on `ℝ^n`, then
`min_{x ∈ ℤ^n \ {0}} F(x) ≤ (4/3)^{(n-1)/2} (det F)^{1/n}`."

Raised to the power `n`, this reads
`(min F)^n ≤ (4/3)^{n(n-1)/2} det F`. `hermite_bound` proves this for forms
with integer values on a lattice, which is the case needed here. Since
`n choose 2 = n(n-1)/2`, `hermite_bound` with `p = a` and `q = 1` is exactly
the displayed inequality, multiplied out to avoid real roots.

Platonov and Rapinchuk state the theorem without proof. The proof here is
Hermite's classical induction: project away from a minimal vector. The
statement `exists_reduced_basis` and its proof are the standard consequence
of the same induction. Both proofs were written for this module.

## Setting

- `L` is an additive commutative group, viewed as a `ℤ`-module. A basis is
  a Mathlib `Basis (Fin d) ℤ L`.
- `β : LinearMap.BilinForm ℤ L` is a bilinear form. `β.IsSymm` is
  Mathlib's symmetry predicate.
- `BilinForm.toMatrix b β` is the Gram matrix `(β (b i) (b j))_{i,j}`.

## Declarations

### Positive definiteness and basic facts

- `IsPosDef β` (definition): `0 < β x x` for every `x ≠ 0`.
  `isPosDef_iff_posDef` shows that this is, by definition, Mathlib's
  `QuadraticMap.PosDef` for the quadratic map `x ↦ β x x`.
  `IsPosDef.nonneg`: `0 ≤ β x x` for all `x`.
- `det_toMatrix_eq`: the Gram determinants in two bases agree. The
  change-of-basis matrix `P` has `det P = ±1`, and the Gram matrix changes
  to `Pᵀ G P`.
- `exists_isMin`: if `L ≠ 0`, some nonzero `v` minimizes `β(x,x)` over the
  nonzero `x`. The values are positive integers, so `Nat.find` applies.
- `apply_smul_smul`: `β(k y, k y) = k² β(y,y)`.
- `mem_span_of_smul_eq` (strong primitivity of a minimal vector), for
  torsion-free `L`: if `v` is minimal, `k ≠ 0` and `k x = m v`, then `x` is
  an integer multiple of `v`.
  - Proof: divide `k` and `m` by their gcd to get coprime `k', m'` with
    `k' x = m' v`. Choose `u k' + w m' = 1` and set `y = u v + w x`. Then
    `k' y = v`, so `β(v,v) = k'² β(y,y) ≥ k'² β(v,v)` by minimality. Hence
    `k'² = 1`, and `x = k'² x = k' m' v`.
- `exists_abs_two_mul_sub_le`: for `a > 0` and any `b` there is `t` with
  `|2 (b - t a)| ≤ a` (rounding `b / a` to the nearest integer).

### The projected form

For `v ∈ L`, write `a = β(v,v)` and let `ℤ ∙ v` be the span of `v`.

- `projForm β v` (definition): the form
  `(x, y) ↦ a β(x,y) - β(x,v) β(y,v)` on `L` (`projForm_apply`). It vanishes
  when either argument is `v` (`projForm_left` uses symmetry,
  `projForm_right` does not).
- `projFormRight β v` (definition): `projForm β v` with its second argument
  descended to `L ⧸ ℤ ∙ v`.
- `quotForm β hs v` (definition): the form on `L ⧸ ℤ ∙ v` induced by
  `projForm β v`, for symmetric `β`. On classes of `x` and `y` it is
  `a β(x,y) - β(x,v) β(y,v)` (`quotForm_mk`). It is symmetric
  (`quotForm_isSymm`).
- `quotForm_mk_self`: the identity
  `a (a β(x,x) - β(x,v)²) = β(a x - β(x,v) v, a x - β(x,v) v)`.
- `sq_le_mul` (Cauchy–Schwarz): for symmetric positive definite `β`,
  `β(x,y)² ≤ β(x,x) β(y,y)`. It follows from `quotForm_mk_self` with the
  roles of `x` and `y` exchanged.

From here on `L` is torsion-free.

- `isTorsionFree_quotient`: if `v` is a nonzero minimal vector, then
  `L ⧸ ℤ ∙ v` is torsion-free. This is a restatement of
  `mem_span_of_smul_eq`.
- `quotForm_isPosDef`: for such `v`, `quotForm β hs v` is positive
  definite. If the class of `x` is nonzero, then `a x - β(x,v) v ≠ 0`
  (otherwise `a` times the class vanishes in a torsion-free quotient), so
  `quotForm_mk_self` gives `a · β'(x,x) > 0`.
- `consBasis hv y hy hyb` (definition): if `v ≠ 0` and the classes of
  `y 0, …, y (n-1)` form a basis `hy` of `L ⧸ ℤ ∙ v`, then
  `v, y 0, …, y (n-1)` is a basis of `L` indexed by `Fin (n + 1)`
  (`consBasis_zero`, `consBasis_succ`).

### The Gram determinant relation

`mul_det_quotForm`: with `consBasis` as above and `β'` = `quotForm β hs v`,

`a · det(Gram of β' in hy) = a^n · det(Gram of β in consBasis)`.

Proof: let `S` be the Gram matrix of `β` in the basis `v, y`. Let `E` be
the lower triangular matrix with first row `(1, 0, …, 0)` and row `i + 1`
equal to `a e_{i+1} - β(y_i, v) e_0`, so `det E = a^n`
(`Matrix.det_succ_row_zero`). The product `E S` has first column
`(a, 0, …, 0)`, and its lower right `n × n` block is the Gram matrix of
`β'`. Expanding along the first column (`Matrix.det_succ_column_zero`)
gives `det(E S) = a · det β'`.

### Hermite's inequality

- `exists_lift`: every class `z ∈ L ⧸ ℤ ∙ v` has a representative `x` with
  `|2 β(x,v)| ≤ a`.
- `three_mul_sq_le`: if `v` is a nonzero minimal vector and `z ≠ 0`, then
  `3 a² ≤ 4 β'(z,z)`. Take `x` from `exists_lift`. Then `x ≠ 0`, so
  `β(x,x) ≥ a`, and `4 β'(z,z) = 4 a β(x,x) - (2 β(x,v))² ≥ 4a² - a²`.
- `finrank_quotient_add_one`: for finite `L` and `v ≠ 0`,
  `rank(L ⧸ ℤ ∙ v) + 1 = rank L`.
- `hermite_bound d`: for every `L` with a basis `b` of size `d`, every
  symmetric positive definite `β`, and integers `p, q ≥ 0` with
  `p ≤ q β(x,x)` for all `x ≠ 0`:

  `3^(d choose 2) · p^d ≤ 4^(d choose 2) · q^d · det(Gram of β in b)`.

  - Proof by induction on `d`. For `d = 0` both sides are `1`. For
    `d = n + 1`, take a minimal `v` with `a = β(v,v)`. The quotient
    `L ⧸ ℤ ∙ v` is free of rank `n` (torsion-free and finitely generated
    over `ℤ`). By `three_mul_sq_le`, the induction hypothesis applies to
    `β'` with `p = 3a²` and `q = 4`:
    `3^(n choose 2) (3a²)^n ≤ 4^(n choose 2) 4^n det β'`.
  - Multiply by `a` and use the Gram relation `a det β' = a^n det β` and
    `(n+1) choose 2 = (n choose 2) + n`. This gives
    `a^n · 3^((n+1) choose 2) a^(n+1) ≤ a^n · 4^((n+1) choose 2) det β`.
    Cancelling `a^n > 0` gives `3^((n+1) choose 2) a^(n+1) ≤ 4^((n+1) choose 2) det β`.
  - Finally `p ≤ q a` gives `p^(n+1) ≤ q^(n+1) a^(n+1)`.
- `det_pos`: the Gram determinant of a symmetric positive definite form is
  positive (`hermite_bound` with `p = q = 1`).

### Reduction

`exists_reduced_basis n Δ`: there is `C` such that for every `L` with a
basis `b` of size `n`, and every symmetric positive definite `β` with
`det(Gram of β in b) ≤ Δ`, some basis `c` of `L` satisfies
`|β(c i, c j)| ≤ C` for all `i, j`.

Proof by induction on `n`, with `Δ` arbitrary. For `n = 0` there are no
entries. For `n + 1`, let `A = 4^((n+1) choose 2) · Δ`.

- Bound on the minimum: let `v` be minimal with `a = β(v,v)`. By
  `hermite_bound` (with `p = a`, `q = 1`),
  `a ≤ a^(n+1) ≤ 3^((n+1) choose 2) a^(n+1) ≤ 4^((n+1) choose 2) det β ≤ A`.
- Bound on the quotient determinant: by the Gram relation and `det β' > 0`,
  `det β' ≤ a det β' = a^n det β ≤ A^n Δ`.
- The induction hypothesis for the bound `A^n Δ` gives `C'` and a basis
  `c'` of `L ⧸ ℤ ∙ v` with `|β'(c' i, c' j)| ≤ C'`. Lift each `c' i` to
  `y i` with `|2 β(y i, v)| ≤ a` (`exists_lift`), and take
  `c = consBasis hv y c'`.
- Entries, with `C = |C'| + A² + A`:
  - `β(v,v) = a ≤ A`;
  - `|β(v, y j)| = |β(y j, v)| ≤ a ≤ A`;
  - `|β(y i, y j)| ≤ |a β(y i, y j)| = |β'(c' i, c' j) + β(y i,v) β(y j,v)| ≤ C' + A²`.

## Qualifications

- The forms are integer-valued on the lattice. Hermite's inequality for
  real forms on `ℝ^n` (the statement in Platonov–Rapinchuk) is not
  formalized; the constant `(4/3)^{(n-1)/2}` appears only in the
  multiplied-out integer form above.
- The constant `C` in `exists_reduced_basis` is explicit in the proof but
  not optimized; no reduction algorithm (such as LLL or Minkowski
  reduction) is formalized.
- Finiteness of the number of isometry classes, and the application to
  double cosets of definite unitary groups, are not part of this module.
