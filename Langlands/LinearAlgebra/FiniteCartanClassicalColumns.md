# Explicit columns for classical Cartan matrices

This intermediate development constructs nonnegative integral solutions of
`N *ᵥ y = c e_k` for standard Cartan matrices. Such solutions yield necessary
inequalities for a finite Cartan leaf extension.

For type A of rank `n`, the sequence has value
`t*(n-k)` up to `t=k+1`, and `(k+1)*(n+1-t)` thereafter, using zero-based
`k`. It vanishes at zero and `n+1`; its second difference is zero except at
`k+1`, where it is `n+1`. Summation of the tridiagonal row therefore proves
the matrix identity with `c=n+1`. At coordinate `k` the value is
`(k+1)*(n-k)`, so an extension with ordered entries `a,b` must satisfy
`a*b*(k+1)*(n-k) < 2*(n+1)`.

The construction and proof are internal integer calculations from the
Mathlib definitions of the standard matrices. They do not assume a
classification result.

The B and C column sequences have scale two and diagonal value
`2*(k+1)` except at the last vertex, where the value is `n`. The D sequence
has scale four, with diagonal value `4*(k+1)` on the stem and `n` at the two
fork endpoints. The proof writes each B/C/D row as an A-row with its explicit
end correction, then verifies the piecewise linear second differences by
integer arithmetic. All sequences are nonnegative.
