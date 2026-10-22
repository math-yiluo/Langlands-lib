# Shahidi's block Weyl element and rectangular radicals

This module implements the matrix geometry used in equations (0.1)–(0.3) of
F. Shahidi, *Fourier transforms of intertwining operators and Plancherel measures
for GL(n)*, American Journal of Mathematics 106 (1984), 67–111, printed
pages 71–72. The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 99. The matrix constructions and proofs below also work in
zero rank and over every commutative ring; the source's analytic applications
use positive ranks and a non-archimedean local field.

## Weyl representative

All declarations are in `Langlands.Shahidi`. `swapRank m n R` reindexes the
actual group of invertible matrices from `Fin (n + m)` to `Fin (m + n)` without
changing the numerical order of entries. This is only a transport of total rank.
`blockWeylPermutation` instead exchanges the two consecutive coordinate blocks.
`blockWeyl m n R` is its all-positive permutation matrix:

\[
w_{m,n}=\begin{pmatrix}0_{m,n}&I_m\\ I_n&0_{n,m}\end{pmatrix}.
\]

Here row blocks have sizes `(m,n)` and column blocks have sizes `(n,m)`.
In particular this is not generally an involution when viewed as a permutation
of the single total-rank index set. The four `blockWeyl_*` entry lemmas specify
this convention, including the exact casts between the two total-rank types.
`blockWeyl_conjugate_blockSum` proves

\[
w_{m,n}\operatorname{diag}(g,h)w_{m,n}^{-1}
  =\operatorname{diag}(h,g),\qquad g\in GL_n(R),\ h\in GL_m(R),
\]

with the source diagonal transported by `swapRank`.

## Rectangular radicals

`upper m n R a` is the actual invertible matrix
`[[I_m,a],[0,I_n]]` for an `m` by `n` matrix `a`. Its inverse is constructed
explicitly using `-a`. Its four blocks, zero, addition, inverse, and injectivity
are proved. `upperHom` is the multiplicative homomorphism from the additive
matrix space (with `Multiplicative` as the type synonym), and `upperRadical`
is its image subgroup.

`intertwiningUnipotent m n R a` transports `upper n m R a` to total rank
`m+n`. Thus its parameter has size `n` by `m`; it is the exchanged upper
radical `U'` used in the source's intertwining integral (0.1).
`intertwiningHom` and `intertwiningRadical` give its homomorphism and image
subgroup, and the coordinate map is proved injective and compatible with zero,
addition, and inverse. It is essential to exchange the block sizes: for
unequal ranks, the original upper radical `U` and this `U'` occupy different
matrix positions. The source describes `U'` as the transpose of the conjugate
of `U` by the long Weyl element; this module directly constructs the resulting
exchanged upper matrices, without asserting a separate equality between those
subgroup presentations.

`lower m n R a` is defined by
`w_(m,n) * intertwiningUnipotent a * w_(m,n)^(-1)`.
Its entry lemmas prove that it is `[[I_m,0],[a,I_n]]`, and `lower_transpose`
identifies it with the transpose of `upper m n R a.transpose`. This `lower`
uses the original row partition `(m,n)`; it is an auxiliary construction,
not a renaming of the source's subgroup `V = w_long U w_long^(-1)`, whose
partition is exchanged.

## Intrinsic proofs and topology

These matrix identities are internal consequences of the source's explicit
matrices, not additional analytic theorems attributed to the paper. The proofs
use Mathlib block multiplication, inverse matrices with negated off-diagonal
blocks, the Library permutation-entry formulas, and the two cases of each
finite block index. The conjugation identity follows by evaluating entries at
the inverse permutation. No determinant nonvanishing is postulated.

For a topological commutative ring, `continuous_upper`,
`continuous_intertwiningUnipotent`, and `continuous_lower` prove continuity into
the existing topology on matrix units. For `upper`, both the matrix and its
inverse have continuous entries; reindexing and multiplication give the other
two results. These results supply the coordinate maps needed for subsequent
integrals. This module defines no measure, induced representation, intertwining
integral, Jacquet functional, or local coefficient, and asserts no convergence
or comparison theorem.

The rectangular unit matrix is the existing
`GeneralLinear.sumBlockUnipotent` from
[`Group/GL/BlockUnipotent`](../../Group/GL/BlockUnipotent.md), reindexed by
`finSumFinEquiv`. The same construction is imported by the automorphic
constant-term module.
