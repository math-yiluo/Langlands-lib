# The convergent germs of a complete locally compact field form a henselian ring

Author: Worker 78.

Let `K` be a nontrivially normed field that is locally compact and complete, and let `𝒰` be
an ultrafilter on a type `I` (in the same universe as `K`). The Library's
`LocalFieldUltrapower.lean` defines the ultrapower `UltrapowerField K 𝒰 = K^I/𝒰`, the valuation
subring `convergentGerms K 𝒰 hnd` of germs that converge along `𝒰` (where
`hnd : ¬ DiscreteTopology K`), and the `K`-algebra map `standardPart` sending a convergent germ
to its limit. The first three results below do not assume completeness; it is assumed only
for `convergentGerms_henselian`. This module proves that
the convergent germs form a henselian local ring. It is an auxiliary result with internal
provenance, used to lift points of étale charts over the convergent germs.

## Results

- `isUnit_of_standardPart_ne_zero`: a convergent germ with nonzero limit is a unit; the inverse
  is the germ of the pointwise inverses, which converge to the inverse limit.
- `mem_maximalIdeal_convergentGerms_iff`: the maximal ideal is the kernel of `standardPart`.
- `eval_ultrapowerMap`: evaluating a monic polynomial with germ coefficients at a germ is the
  germ of the pointwise evaluations.
- `convergentGerms_henselian`: `HenselianLocalRing (convergentGerms K 𝒰 hnd)`.

## Proof of `convergentGerms_henselian`

Let `f` be a monic polynomial of degree `n` over the convergent germs and `a₀` a germ with
`f(a₀)` in the maximal ideal and `f'(a₀)` a unit. Applying `standardPart` (a ring map) shows
that the reduced polynomial `f̄` over `K`, with coefficients `c_k`, has the simple root
`ρ(a₀)`; the degree is positive because a monic constant polynomial is `1`. Represent the
coefficients of `f` by families `g_k : I → K`; they converge to `c_k` along `𝒰`. The Library's
`monicSimpleRootContinuity` (continuity of simple roots of monic polynomials over complete
normed fields, `SimpleRootContinuityProof.lean`) gives a function `ψ` of the coefficient
vector, continuous at `c` with `ψ(c) = ρ(a₀)`, which is a root of the monic polynomial with
those coefficients near `c`. The family `a_i = ψ((g_k i)_k)` converges to `ρ(a₀)`, hence its
germ `α` is a convergent germ with `ρ(α) = ρ(a₀)`, so `α − a₀` lies in the maximal ideal, and
`f(α) = 0` because the pointwise evaluations vanish for `𝒰`-almost all `i`
(`eval_ultrapowerMap`).
