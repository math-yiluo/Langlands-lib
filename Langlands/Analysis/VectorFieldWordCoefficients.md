# Coordinate coefficients of words in vector fields

Let `V : Fin n → F → F` be vector fields on `F = EuclideanSpace ℝ (Fin d)`. A word
`w = [i₁, …, iₖ]` in `Fin n` acts on functions by the composite `∂_{V i₁} ∘ ⋯ ∘ ∂_{V iₖ}` of
directional derivatives. This module writes that composite as a combination of ordered coordinate
derivatives `D^k u x (e (W 0), …, e (W (k-1)))`. Here `e` is the standard basis and
`W : Fin k → Fin d`. The module also identifies the top-order coefficients. It is an internal
calculus tool for the Lie group interior estimate. It has no literature source.

## Definition

`vectorFieldWordCoeff V w k W x : ℂ` is the coefficient of `D^k u x (e (W 0), …, e (W (k-1)))`.
It is defined by recursion on the word:
- the empty word has coefficient `1` in order `0` and `0` in every positive order;
- `vectorFieldWordCoeff V (i :: w) 0 W x` is the derivative of `vectorFieldWordCoeff V w 0 W`
  at `x` along `V i x`;
- `vectorFieldWordCoeff V (i :: w) (k+1) W x` is the derivative of
  `vectorFieldWordCoeff V w (k+1) W` along `V i x`, plus the `W 0`-th coordinate of `V i x`
  times `vectorFieldWordCoeff V w k (Fin.tail W) x`.

This is the product rule: differentiating `a(x) · D^k u x (…)` along `V i` either
differentiates the coefficient, or adds one more derivative of `u` in the first slot along
`V i x = ∑_j (V i x)_j e_j`.

## Results

- `vectorFieldWordCoeff_eq_zero`: coefficients of order `k > w.length` vanish identically.
  Proof by induction on the word.
- `contDiffOn_vectorFieldWordCoeff`: on an open set where every `V i` is `C^∞`, every coefficient
  is `C^∞`. Proof by induction on the word, using `ContDiffOn.fderiv_of_isOpen`.
- `sum_coord_mul_iteratedFDeriv_cons`: `∑_j (v_j) D^{k+1} u x (e_j, e_{W 0}, …)` equals the
  derivative at `x` along `v` of `y ↦ D^k u y (e_{W 0}, …)`, for `u` smooth at `x`. The proof
  uses `iteratedFDeriv_succ_apply_left` and the basis expansion of `v`.
- `sum_fun_fin_succ`: a sum over `(k+1)`-tuples splits into the first entry and the remaining
  `k`-tuple (via `Fin.consEquiv`).
- `vectorFieldWord_expansion`: let `G` be a word-indexed family of functions with `G [] = u` and
  `G (i :: w) x = fderiv (G w) x (V i x)` on an open set `S`, where `u` and the `V i` are smooth.
  Then for `x ∈ S` and any `N ≥ w.length`, `G w x` is the sum over `k ≤ N` and
  `W : Fin k → Fin d` of `vectorFieldWordCoeff V w k W x * D^k u x (e ∘ W)`.
  - **Proof.** Induction on the word. In the step the expansion for `w` holds near `x`, so its
    derivative along `V i x` is computed term by term with the product rule (private lemma
    `fderiv_wordArray`). The derivatives of the tensors are rewritten with
    `sum_coord_mul_iteratedFDeriv_cons` (private lemma `prepend_sum`). The resulting sums are
    reindexed by one order and matched with the recursion. The vanishing above order
    `w.length` removes the boundary term.
- `vectorFieldWordCoeff_symbol`: for a real covector `ξ`, the sum over `W : Fin w.length → Fin d`
  of `vectorFieldWordCoeff V w w.length W x * ∏_j ξ (e (W j))` equals
  `∏_{a ∈ w} ξ (V a x)` (as a list product). Induction on the word: in top order only the
  second term of the recursion survives, and `ξ (V i x) = ∑_a (V i x)_a ξ (e a)`.
