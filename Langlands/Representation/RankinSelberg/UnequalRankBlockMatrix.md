# Rank-transported unequal-rank JPSS block matrices

This module defines one function,
`Langlands.RankinSelberg.AdjacentBlockReduction.blockMatrixAt`. It is the
published JPSS block matrix `unequalRankMatrix j k g Y` from
`Langlands.Representation.RankinSelberg.QuotientIntegrals`, with its
natural-number rank rewritten along an equation. It is the only declaration in
the module, and the module imports only `QuotientIntegrals`.

## Definition

The inputs are:

- an arbitrary field `F` in an arbitrary universe `uF`, with no topology,
  absolute value or measure;
- natural numbers `n`, `j` and `k`, each of which may be zero, and a natural
  number `r`;
- an equation `hr : r = n + (j + k + 1)`, which determines `r` from `n`, `j`
  and `k` and forces `r ≥ 1`;
- a matrix `g : Langlands.GeneralLinear (n + 1) F`;
- a rectangular matrix `Y : Matrix (Fin j) (Fin (n + 1)) F`.

The value `blockMatrixAt j k hr g Y` is an element of
`Langlands.GeneralLinear (r + 1) F`. The body substitutes `r` by
`n + (j + k + 1)` using `hr` and then returns `unequalRankMatrix j k g Y`. Hence:

- when `hr` is `rfl`, so that `r` is literally `n + (j + k + 1)`, the value is
  definitionally `unequalRankMatrix j k g Y`;
- for any `hr`, eliminating `hr` turns the value into exactly
  `unequalRankMatrix j k g Y`.

The equation `hr` only transports a natural-number rank. It changes no entry,
block or multiplication, and nothing else depends on it.

## The underlying block matrix

`unequalRankMatrix j k g Y` is defined in `QuotientIntegrals` as
`diag(g, I_(j+k+1)) * (1 + X)`. Here `X` has the entries of `Y` in rows
`n + 1` through `n + j` (counting from zero) and columns `0` through `n`, and
zero entries elsewhere. That module proves its entries are exactly the blocks

```
[ g  0    0       ]
[ Y  I_j  0       ]
[ 0  0    I_(k+1) ]
```

of the large group `GL_(n + (j + k + 1) + 1)`. In the source notation of
Jacquet, Piatetski-Shapiro and Shalika, the small rank is `t = n + 1` and the
large rank is called `r`. That source large rank is the Lean number `r + 1`,
not the Lean number `r`: it equals `t + (j + k + 1) = n + (j + k + 1) + 1`. The
rectangular block has `j` rows, and the final identity block has size
`k + 1 = (r + 1) - t - j`, in terms of the Lean `r`. For example,
`n = j = k = 0` gives Lean `r = 1` and the large group `GL_2`.

All zero dimensions are kept. `n = 0` gives small rank one. `j = 0` gives no
rectangular rows. Then `Y` is the unique empty matrix and the value is the
diagonal inclusion `diag(g, I_(k+1))`. `k = 0` gives a final identity block of
size one. The equation forces the large rank `r + 1` to exceed the small rank
`n + 1` by `j + k + 1 ≥ 1`. So equal ranks are not covered, as for
`unequalRankMatrix`.

## Why the rank is transported

`unequalRankMatrix j k g Y` lives in a group whose rank expression
`n + (j + k + 1) + 1` depends on the split of `j + k + 1` into `j` and `k`. The
adjacent pairs `(j + 1, k)` and `(j, k + 1)` give the same number, but the two
expressions are not syntactically equal. An integration helper that fixes one
large group `GL_(r + 1)` and compares block matrices for adjacent `j` therefore
needs the two matrices in one type. `blockMatrixAt` gives that common type.
Each split supplies its own proof of `r = n + (j + k + 1)`.

This module proves no comparison of block matrices. In particular, it does not
state that a zero final rectangular row gives the neighbouring block matrix.
It also asserts nothing about entries beyond the definition.

## Scope

This is a purely algebraic construction. The module makes no topological,
representation-theoretic, measure-theoretic or analytic assertion. It introduces
no integral, convergence statement, support statement, Fourier transform,
rational continuation or functional equation.

## Provenance

This is a derived/internal definition. It is not printed in the original
literature. Its mathematical content is the existing published
`unequalRankMatrix`, whose correspondence with the JPSS block matrix is
documented in `QuotientIntegrals.md`. The only new ingredient is the
natural-number rank transport, which is a formalization device.

The original motivation is an argument that fixes the large rank and varies the
number `j` of rectangular rows:

- Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions*
  (1983), source `jpss-1983-rankin-selberg`, SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. The
  relevant passage is the proof of Theorem (2.7) for `r > t`, printed pages
  393–395 (PDF pages 28–30, one-based). The integrals use the block matrix
  `[g,0,0; x,1_j,0; 0,0,1]` in the source group `GL_r`, with
  `0 ≤ j ≤ r - t - 1` (source notation; here source `r` is Lean `r + 1`). The
  unnumbered Lemma on pp.394–395 relates integrals for `j` and `j - 1`. The
  proof concludes that `I_j = I_(j-1)` and `P_j = P_(j-1)`.
- Jacquet, Piatetski-Shapiro and Shalika, *Automorphic Forms on GL(3) I*
  (1979), source `jps-1979-gl3-i`, SHA-256
  `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
  Printed pages 188–190 (PDF pages 21–23, one-based) contain the integrals
  (4.1.1)–(4.1.3), Proposition (4.1.4) and Lemma (4.1.5). They give the chain
  of ideal inclusions between adjacent values of `j` on p.190.

In both sources the large rank is a single fixed number while `j` varies. In
Lean, that fixed number corresponds to `r + 1`, the rank of the codomain
`GL_(r + 1)`. Each `j` comes with its own equation `r = n + (j + k + 1)`, so
that `n + (j + k + 1) + 1 = r + 1`. The interface `blockMatrixAt` itself does
not appear verbatim in either source.

## Authorship

Worker 180 designed this definition, with its name, signature and body, in
shared draft revision 11 of task `798cefd9-ab16-4562-ab1a-085680064306`. There
it supports the adjacent-block integration helpers. Worker 381 extracted it
unchanged into this focused module and wrote this documentation. The
surrounding unfinished proof file is not copied or imported.
