# Symmetry and nesting of iterated derivatives of finitely smooth functions

Module `Langlands.Analysis.SmoothIteratedFDerivSymm`, namespace
`Langlands.Analysis`. It imports only Mathlib.

## Conventions

`𝕜` is `ℝ` or `ℂ` (`RCLike 𝕜`). `E` and `F` are normed spaces over `𝕜`
(`NormedAddCommGroup` with `NormedSpace 𝕜 E`). They may be
infinite-dimensional and need not be complete, and `F` may lie in any
universe. `D^k f(x)` means Mathlib's `iteratedFDeriv 𝕜 k f x`, a
continuous `k`-multilinear map `(Fin k → E) → F`. A word of length `k` is a
map `v : Fin k → E`, and `D^k f(x) v` is the derivative in the directions
`v 0, …, v (k - 1)`.

Smoothness levels `n` live in `WithTop ℕ∞` (Mathlib's `ℕ∞ω`), with
`open scoped ContDiff`. Apart from the last-two swap, which assumes `C^2`,
and the combinatorial identity `append_comp_finAddFlip`, every result below
takes an arbitrary level `n` and finite orders bounded by `n` (`k ≤ n`,
`j + p ≤ n` or `m + p ≤ n`). In particular it applies to `C^k` functions for
finite `k` and to `ContDiff 𝕜 ∞` functions. Here `∞` is the `C^∞` level, not
the analytic level `ω`, and no analyticity is assumed anywhere.

`Fin.append m v : Fin (j + p) → E` is the concatenation of the words
`m : Fin j → E` and `v : Fin p → E`: first the letters of `m`, then those
of `v`.

## Definition

- `iteratedLineDeriv 𝕜 p f v x := iteratedFDeriv 𝕜 p f x v`, for `p : ℕ`,
  `f : E → F`, `v : Fin p → E` and `x : E`. It is the ordered iterated
  directional derivative `∂_{v 0} ⋯ ∂_{v (p - 1)} f` at `x`, viewed as a
  function of `x` with the word `v` fixed. `iteratedLineDeriv_apply` is the
  defining equation, which holds by `rfl`.

The definition adds no new content. It only names the function
`x ↦ D^p f(x) v`, so that it can be differentiated again.

## Results

### Symmetry

- `iteratedFDeriv_comp_swap_last`: if `f` is `C^2` at `x`, then for every
  `m` and every word `v : Fin (m + 2) → E`, swapping the last two letters of
  `v` does not change `D^(m+2) f(x) v`. This holds although `f` is only
  assumed `C^2` at `x`. The second derivative `G = D(Df)` agrees near `x`
  with its flip, by Mathlib's `ContDiffAt.isSymmSndFDerivAt` applied at
  nearby points. So the `m`-th derivatives of `G` and of its flip agree at
  `x`, and composing with the flip, which is a fixed linear isometry,
  commutes with differentiation.
- `iteratedFDeriv_comp_perm_of_contDiffAt` (**symmetry**): if `f` is `C^n` at
  `x` and `k ≤ n`, then for every word `v : Fin k → E` and every permutation
  `σ` of `Fin k`,
  `iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v`.
- `iteratedFDeriv_comp_perm_of_contDiffOn`: the same at every point of an
  open set `s` on which `f` is `ContDiffOn 𝕜 n`.
- `iteratedFDeriv_comp_equiv_of_contDiffAt`: the same for a bijection
  `e : Fin k ≃ Fin l`. Such a bijection forces `k = l`, and the statement
  reads `iteratedFDeriv 𝕜 k f x (v ∘ e) = iteratedFDeriv 𝕜 l f x v` for
  `v : Fin l → E` and `l ≤ n`.

### Nesting

- `iteratedFDeriv_append_of_contDiffAt` (**nesting identity**): if `f` is
  `C^n` at `x` and `j + p ≤ n`, then for `m : Fin j → E` and `v : Fin p → E`,
  `iteratedFDeriv 𝕜 (j + p) f x (Fin.append m v) =
  iteratedFDeriv 𝕜 j (fun y => iteratedFDeriv 𝕜 p f y v) x m`.
  That is, differentiating the line derivative `y ↦ D^p f(y) v` a further `j`
  times along `m` gives the `(j + p)`-th derivative of `f` on the
  concatenated word `m ++ v`.
- `iteratedFDeriv_append_of_contDiffOn`: the same at every point of an open
  set on which `f` is `ContDiffOn 𝕜 n`.
- `append_comp_finAddFlip`: for words over any type `α`,
  `Fin.append v m ∘ finAddFlip = Fin.append m v`. This is a combinatorial
  identity with no derivatives.
- `iteratedFDeriv_append_comm_of_contDiffAt`: if `f` is `C^n` at `x` and
  `j + p ≤ n`, then
  `iteratedFDeriv 𝕜 (j + p) f x (Fin.append m v) =
  iteratedFDeriv 𝕜 (p + j) f x (Fin.append v m)`. This follows from the two
  previous items and symmetry.

### Line derivatives

All statements in this subsection are on an open set `s`.

- `contDiffOn_iteratedLineDeriv`: if `f` is `ContDiffOn 𝕜 n` on `s` and
  `m + p ≤ n` (in `ℕ∞ω`), then `iteratedLineDeriv 𝕜 p f v` is
  `ContDiffOn 𝕜 m` on `s` for every word `v : Fin p → E`.
- `contDiffOn_infty_iteratedLineDeriv`: if `f` is `ContDiffOn 𝕜 ∞` on `s`,
  then every `iteratedLineDeriv 𝕜 p f v` is `ContDiffOn 𝕜 ∞` on `s`.
- `iteratedLineDeriv_iteratedLineDeriv`: if `f` is `ContDiffOn 𝕜 n` on `s`,
  `x ∈ s` and `j + p ≤ n`, then
  `iteratedLineDeriv 𝕜 j (iteratedLineDeriv 𝕜 p f v) m x =
  iteratedLineDeriv 𝕜 (j + p) f (Fin.append m v) x`.
- `iteratedLineDeriv_comp_perm`: if `f` is `ContDiffOn 𝕜 n` on `s`, `x ∈ s`
  and `k ≤ n`, then
  `iteratedLineDeriv 𝕜 k f (v ∘ σ) x = iteratedLineDeriv 𝕜 k f v x` for every
  permutation `σ` of `Fin k`.

Together, the last two items say this. At a point of `s`, with
`j + p ≤ n`, the nested line derivative
`iteratedLineDeriv 𝕜 j (iteratedLineDeriv 𝕜 p f v) m` equals the single line
derivative along `Fin.append m v`, and that value does not change when the
letters of the word are permuted.

## Scope

Mathlib (commit `5ed29652`) states symmetry of iterated derivatives of all
orders only for analytic functions (`ContDiffAt.iteratedFDeriv_comp_perm`
with smoothness `ω`, `AnalyticOn.iteratedFDeriv_comp_perm`, and their
`iteratedFDerivWithin` versions). For finite smoothness it states only the
second-order case (`ContDiffAt.isSymmSndFDerivAt`, and
`ContDiffWithinAt.isSymmSndFDerivWithinAt` within sets). This module extends
symmetry to all orders under finite smoothness, over `ℝ` and `ℂ`.

The module proves no estimate, no regularity statement and no result about
differential operators. It treats only `ℝ` and `ℂ`. Over other nontrivially
normed fields, Mathlib's second-order symmetry asks for analyticity (smoothness
`minSmoothness 𝕜 2`, which is `ω` there), and the module says nothing about
that case.

## Provenance

This is internal, derived content. The theorem is the classical symmetry of
higher derivatives of `C^k` maps between normed spaces, which follows from
Schwarz's theorem for second derivatives by induction on the order. No
literature statement is formalized verbatim, and the Lean proof is
independent of any text. The module was written to support the scalar
elliptic regularity chain of task `d7081753-2858-442a-bd34-eda72b059529`.
There, cutoff and factorial estimates sum over words of basis directions and
need to reorder and regroup iterated derivatives of `ContDiffOn ℝ ∞`
functions on balls.

## Proof outline

- **Last-two swap.** `D^(m+2) f(x) v` equals
  `D^m G(x) (init (init v)) (v (m)) (v (m+1))`, by unfolding twice with
  `iteratedFDeriv_succ_apply_right`, where `G = D(Df)`. Near `x`, `G` equals
  its composition with `ContinuousLinearMap.flipₗᵢ`. This uses Mathlib's
  second-order symmetry at nearby points, which needs `C^2` near `x`, and
  `ContDiffAt` gives that. `Filter.EventuallyEq.iteratedFDeriv` and
  `ContinuousLinearEquiv.iteratedFDeriv_comp_left` then swap the last two
  arguments.
- **All permutations** (`iteratedFDeriv_comp_perm_aux`, private). The proof is
  by induction on `k`, generalized over the codomain `F`. The permutations
  that preserve `D^(k+1) f(x)` form a submonoid of `Perm (Fin (k + 1))`. This
  submonoid contains:
  - every permutation fixing the last element. Such a permutation acts on the
    first `k` letters, and these are the arguments of `D^k (Df)(x)`. The
    induction hypothesis applies to `Df`, which is `C^k` at `x`.
  - every adjacent transposition `swap i.castSucc i.succ`. The last one is
    the last-two swap, and the others fix the last element.

  Mathlib's `Equiv.Perm.mclosure_swap_castSucc_succ` says adjacent
  transpositions generate the symmetric group as a monoid. So the submonoid
  is everything.
- **Universes.** The induction passes from `f : E → F` to `Df : E → (E →L F)`,
  whose codomain lies in universe `max uE uF`. The private auxiliary lemmas are
  therefore stated for codomains in `Type (max uE uF)`. The public theorems
  transfer to an arbitrary `F : Type uF` by composing with
  `ContinuousLinearEquiv.ulift : ULift F ≃L[𝕜] F`, which commutes with
  `iteratedFDeriv` and is injective.
- **Nesting** (`iteratedFDeriv_append_aux`, private). The proof is by
  induction on `p`, again over codomains in `Type (max uE uF)` with the same
  `ULift` transfer. The step writes `D^(p+1) f(y) v` as
  `D^p (Df)(y) (init v) (v p)`. That is a fixed continuous linear map, namely
  evaluation at `v p`, applied to a `C^j` function. So
  `ContinuousLinearMap.iteratedFDeriv_comp_left` moves it outside the `j`-th
  derivative. The induction hypothesis for `Df`, together with
  `Fin.append m v = Fin.snoc (Fin.append m (init v)) (v p)`, closes the step.
- **Smoothness of line derivatives.** Use
  `ContDiffAt.iteratedFDeriv_right` and then evaluate with the continuous
  linear map `ContinuousMultilinearMap.apply`.
