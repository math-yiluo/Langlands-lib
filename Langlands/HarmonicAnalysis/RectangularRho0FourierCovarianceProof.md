# Full Fourier covariance of the transported action (JPSS formula (7)): proof

Worker 753 wrote this module for task `72d7fdf8-090b-4d38-bb33-fda5da1e17d9`.
`Langlands.HarmonicAnalysis.rectangularRho0FourierCovariance.{uK}` proves
exactly the closed published proposition
[`RectangularRho0FourierCovarianceStatement`](RectangularRho0FourierCovarianceStatement.md).
The proof keeps the implicit carrier `K : Type uK`, all eight typeclass
hypotheses on it, every unitary additive character `ψ`, every supplied
additive Haar measure `μ`, every rank `n : ℕ` (including `n = 0`), the sole
premise `hsd : IsSelfDual ψ μ`, every `g : Langlands.GeneralLinear (n + 1) K`
and every `Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)`. It proves
the equality of Schwartz–Bruhat functions

```text
rectangularFourierEquiv ψ μ n (n + 1) hsd (rectangularRho0 ψ μ n hsd g Φ) =
  ((((MeasureTheory.distribHaarChar K
      (Langlands.GeneralLinear.determinant g) : ℝ) : ℂ) ^ n)⁻¹) •
    rectangularRho0 ψ μ n hsd (Langlands.GeneralLinear.inverseTranspose (n + 1) K g)
      (rectangularFourierEquiv ψ μ n (n + 1) hsd Φ).
```

Write `F = rectangularFourierEquiv ψ μ n (n + 1) hsd`,
`T = partialFourierEquiv ψ μ n hsd`, `ρ = rectangularRho0 ψ μ n hsd`,
`R_g = rectangularTranslate g`, `gι` for
`Langlands.GeneralLinear.inverseTranspose (n + 1) K g`, and `c` for the
displayed scalar `((Δ (det g) : ℂ) ^ n)⁻¹` with
`Δ = MeasureTheory.distribHaarChar K`. The target pair and every pair it
imports are used unchanged.

## Imported results

All of the following are published results, imported by Lean name.

- `rectangularFourierCovariance`, from
  [`RectangularFourierCovarianceProof`](RectangularFourierCovarianceProof.md),
  proves
  [`RectangularFourierCovarianceStatement`](RectangularFourierCovarianceStatement.md):
  for all ranks `r s`, every `h : Langlands.GeneralLinear s K` and every
  `Ψ`, the chosen full equivalence at ranks `r, s` satisfies
  `F (R_h Ψ) = ((Δ (det h) : ℂ) ^ r)⁻¹ • R_hι (F Ψ)`, where `hι` is the
  inverse transpose of `h`. It is applied here at `r = n`, `s = n + 1` and
  `h = g`. Its scalar is then literally the scalar `c` of the target.
- `rectangularFourierCommutation`, from
  [`RectangularFourierCommutationProof`](RectangularFourierCommutationProof.md),
  proves
  [`RectangularFourierCommutationStatement`](RectangularFourierCommutationStatement.md):
  `F (T Ψ) = T (F Ψ)` for every `Ψ` in the `n × (n + 1)` Schwartz space.
- `rectangularRho0_apply`, from
  [`PartialFourierEquiv`](PartialFourierEquiv.md), states (by `rfl`) that
  `ρ g Φ = T (R_g (T.symm Φ))`.
- From Mathlib: `LinearEquiv.injective`, `LinearEquiv.apply_symm_apply` and
  `map_smul` for the complex-linear equivalence `T`.

Both prerequisite theorems take exactly the same field telescope, `ψ`, `μ`
and `hsd` as the target, so they are applied to the hypotheses of the target
with no additional premise.

## The proof

After introducing the telescope, the proof names `F` and `T` with `set`.

1. **Commutation.** `hcomm : ∀ Ψ, F (T Ψ) = T (F Ψ)` is
   `rectangularFourierCommutation ψ μ n hsd`.
2. **Commutation with the inverse.** `hcommSymm : ∀ Ψ, F (T.symm Ψ) =
   T.symm (F Ψ)`. Since `T` is injective, it suffices to show
   `T (F (T.symm Ψ)) = T (T.symm (F Ψ))`. Rewriting the left side backwards
   with `hcomm` gives `F (T (T.symm Ψ))`, and `T.apply_symm_apply` reduces
   both sides to `F Ψ`.
3. **The calculation.** The goal is rewritten in this order:
   - `rectangularRho0_apply` twice, unfolding `ρ g Φ` to
     `T (R_g (T.symm Φ))` on the left and `ρ gι (F Φ)` to
     `T (R_gι (T.symm (F Φ)))` on the right;
   - `hcomm`, giving `T (F (R_g (T.symm Φ)))` on the left;
   - `rectangularFourierCovariance ψ μ n (n + 1) hsd g`, giving
     `T (c • R_gι (F (T.symm Φ)))`;
   - `hcommSymm`, giving `T (c • R_gι (T.symm (F Φ)))`;
   - `map_smul` for `T`, giving `c • T (R_gι (T.symm (F Φ)))`.

   The two sides are then syntactically equal and the rewrite closes the
   goal. This is the calculation

```text
F (ρ g Φ) = F (T (R_g (T.symm Φ)))
          = T (F (R_g (T.symm Φ)))
          = T (c • R_gι (F (T.symm Φ)))
          = c • T (R_gι (T.symm (F Φ)))
          = c • ρ gι (F Φ).
```

No integral, measure or Fourier inversion formula appears in this module;
all analytic content is in the two imported theorems.

## Hypotheses and degenerate rank

The theorem adds no premise to the target. It installs no instance, and in
particular adds no product Borel, sigma-finiteness, second-countability,
inversion-continuity, valuation, p-adic-field or positive-rank hypothesis.
It assumes no covariance or commutation law: both are the published
theorems above. It does not replace the supplied measure, character,
Schwartz space, chosen maps or transported action.

The rank `n = 0` needs no separate case: the argument is uniform in `n`,
and both imported theorems hold for every rank.

A development check reported zero errors and warnings for this module, and
that the theorem depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Scope and source

The target Markdown explains that the statement is a derived generic
chosen-map formulation of formula (7) of H. Jacquet, I. I. Piatetski-Shapiro
and J. A. Shalika, *Rankin-Selberg Convolutions*, Amer. J. Math. 105 (1983),
Section 6.1, printed page 428 (registered as `jpss-1983-rankin-selberg`).
The source derives formula (7) from full Fourier covariance and the fact
`(Φ~)^ = (Φ^)~`, saying only that it "easily follows". The implemented
proof is that derivation, carried out for the chosen maps `F` and `T` and the
transported action `ρ = T ∘ R_g ∘ T.symm`.

This module does not identify the intrinsic Haar character `Δ` with the
normalized absolute value of a non-archimedean local field. It contains no
vector-valued models, star transforms, matrix or Whittaker comparisons, or
gamma or L-factor analytics.
