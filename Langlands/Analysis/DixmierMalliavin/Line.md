# The one-variable Dixmier–Malliavin lemma

`Langlands.Analysis.DixmierMalliavin.Line`. Lemme 2.5 of Dixmier and Malliavin: against smooth
functions whose derivatives are bounded by a given sequence, the Dirac measure at `0` is a
convergent series of derivatives of one smooth function plus a smooth function, both supported in
`[0, ε]`.

## Statement

`Langlands.Analysis.DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add`. For every
`M : ℕ → ℝ` and `ε > 0` there are `c : ℕ → ℝ` and smooth `g h : ℝ → ℂ` with
`tsupport g ⊆ [0, ε]`, `tsupport h ⊆ [0, ε]` and `∑ |c p| · M p < ∞`, such that

`F 0 = (∑' p, c p * ∫ t, F^{(p)} t * g t) + ∫ t, F t * h t`

for every smooth `F : ℝ → ℂ` with `‖F^{(p)} t‖ ≤ M p` for all `p` and all `t ∈ [0, ε]`.

The supports are one-sided: `g` and `h` vanish on `(-∞, 0)`. The lemma is used in
`DirectionalSeries` and `LinearGroup` for `F(t) = f(exp(tX) x)`, where it writes `f` as a sum of
averages of left translates of `f` and of a series of its derivatives in the direction `X`.

## Proof

The objects are those of `ExponentialKernel` and `KernelProduct`: the exponential kernels
`k_{a,r}(t) = a e^{-at} χ_r(t)` cut off smoothly between `r` and `2r`, their remainders
`η_{a,r} = -e^{-at} χ_r'`, the step identity `F(0) = ∫ (F - a⁻¹F') k_{a,r} + ∫ F η_{a,r}` and its
iteration, the stage identity

`F(0) = ∫ (T_{n+1} F) K_n + ∑_{j ≤ n} ∫ F ρ_j`,  `T_{n+1} = ∏_{j ≤ n} (1 - a_j⁻¹ d/dt)`,

where `K_n = k_{a_0,r_0} ⋆ ⋯ ⋆ k_{a_n,r_n}` and `ρ_j` are the remainder kernels.

The radii are `r_j = ε / 2^{j+3}` (`radii`), so that every `K_n` and every `ρ_j` is supported in
`[0, ε/2]` (`supportBound_radii_le`). The weights are `w_0 = 1`, `w_p = 2^{-p} / max 1 |M p|`
(`weight`), so that `∑ w_p |M p|` converges. The rates `a_j` are chosen so that `a_j` satisfies
`IsAdmissibleRate M ε j`:

1. `a_j > 0`;
2. `a_j⁻¹ w_{p-1} ≤ 2^{-(j+1)} w_p` for `1 ≤ p ≤ j + 1`: then the coefficients of
   `∏_{j < n} (1 + a_j⁻¹ X)` stay below the weights for every `n` (`productCoeff_le_weight`, from
   `productCoeff_le_of`);
3. the first `2j + 3` derivatives of `η_{a_j, r_j}` are uniformly at most `2^{-j} / (j + 2)`: with
   (2), the first `n + 1` derivatives of `ρ_{n+1}` are at most `2^{-(n+1)}`
   (`norm_iteratedDeriv_stageRemainder_succ_le_half_pow`);
4. `e^{-a_j r_j} ≤ 2^{-j}`: with `r_j = ε / 2^{j+3}`, successive Fourier transforms of the `K_n`
   differ by a summable amount.

Each condition holds for all large rates (`eventually_isAdmissibleRate`): (2) is a finite set of
lower bounds, (3) holds because the derivatives of `η_{a,r}` tend to `0` uniformly as `a → ∞`, and
(4) because `r_j > 0`. The rates are then chosen by `choose`.

With these choices:

- the coefficients `productCoeff a n p` increase in `n` and are bounded by `w_p`; their limit is
  `limitCoeff p ≤ w_p`, and `c p = (-1)^p limitCoeff p` satisfies `|c p| M p ≤ w_p |M p|`, which is
  summable;
- the `k`-th derivatives of the `ρ_j` are bounded by a summable sequence (`majorant`), so
  `h = ∑ ρ_j` (`remainderSum`) is smooth, supported in `[0, ε/2]`, and `∑_j ∫ F ρ_j = ∫ F h`;
- the Fourier transforms of the `K_n` converge (`tendsto_fourier_kernelProduct`) and
  `|ξ|^m ‖𝓕 K_n(ξ)‖ ≤ ∏_{j<m} a_j / π` for `n ≥ m` (`decay_fourier_kernelProduct`), so by
  `exists_contDiff_weakLimit_of_fourier_decay` the `K_n` converge weakly to a smooth `g` supported
  in `[0, ε/2]`;
- `∫ (T_{n+1} F) K_n = ∑_p signedCoeff a (n+1) p ∫ F^{(p)} K_n`, and this tends to
  `∑_p c_p ∫ F^{(p)} g` by dominated convergence for series, with the bound `w_p |M p|`: here the
  hypothesis on `F` is used, on `[0, ε/2]` only.

Passing to the limit in the stage identity gives the lemma.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §2, Lemme 2.5; page 5 of the English
translation *Factorizations of infinitely differentiable functions and smooth vectors* (translator
not named, with its own page numbers), where it is Lemma 2.5, proved on pages 5–6, with the
supports in `[-ε, ε]` by Remark 2.6, page 6. There the lemma gives, for a sequence `β`, numbers
`α_n ≤ β_n` and `g, h` with `∑_{n ≤ p} (-1)^n α_n δ^{(2n)} ∗ g → δ + h` in `ℰ'(ℝ)`, so only even
orders occur and the supports are two-sided; here every order occurs, the coefficients are summable
against the bounds `M`, and the supports are in `[0, ε]`.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean`, lines 1–395 (the whole
file), of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source file:

- Namespace `GroundTheory.Automorphic` becomes `Langlands.Analysis.DixmierMalliavin`, and
  `…LineKernel` becomes `…DixmierMalliavin.Line`.
- `exists_dixmierMalliavin_line` is renamed `exists_dirac_eq_tsum_iteratedDeriv_add`, and its
  statement is strengthened: the source gives `tsupport g, tsupport h ⊆ [-ε, ε]` and assumes the
  bounds on `F` on `[-ε, ε]`; here the supports are in `[0, ε]` and the bounds are assumed on
  `[0, ε]` only. The proof already gave supports in `[0, ε/2]` and used the bounds only there; the
  auxiliary `hasSum_integral_remainderSum` is restated with its hypothesis on `[0, ε]`.
- Names: `Good` → `IsAdmissibleRate`, `good_pos` → `isAdmissibleRate_pos`, `eventually_good` →
  `eventually_isAdmissibleRate`, `remSum` → `remainderSum`, `climit` → `limitCoeff`, and the names
  of `KernelProduct`; `radii`, `weight`, `majorant` keep their names.
- The file option `linter.unusedSectionVars false` is removed; unused section hypotheses are left
  out with `omit … in`, and uses pass one argument less.
- The deprecated `if_pos`/`if_neg` are replaced by `ite_eq_left`/`ite_eq_right`.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
