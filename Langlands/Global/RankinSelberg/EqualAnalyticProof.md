# Proof of the global analytic theory for equal-rank cuspidal pairs

This module proves `Langlands.Global.RankinSelbergGlobal.EqualAnalyticStatement`. That is the
analytic and functional-equation part of J. W. Cogdell, *Analytic theory of L-functions for
GL_n* (2004), §2.3, Theorem 2.2 (printed p.211; source `cogdell-2004-analytic-theory-gln`). The
proof is the theorem

```
theorem Langlands.Global.RankinSelbergGlobal.EqualAnalytic.equalAnalyticStatement_proof :
    EqualAnalyticStatement.{u}
```

It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Route

Cogdell obtains the analytic properties of `I(s; φ, φ', Φ)` from the Eisenstein series, and
those from Poisson summation for the theta series `Θ'_Φ(a, g) = Σ_(ξ ≠ 0) Φ(a ξ g)` (printed
pp.208–210). The formal proof uses the same ingredients in the classical order of
Jacquet–Shalika. It first unfolds the centre, then splits the integral over
`GL_n(F) \ GL_n(𝔸)` at `|det g| = 1`, then applies Poisson summation on `|det g| < 1` (and, for
the dual integral, on `|det g| ≥ 1`):

1. `equalIntegral_unfold` (module `EqualAnalyticUnfolding`):
   `I(s; φ, φ', Φ) = ∫_(GL_n(F)\GL_n(𝔸)) φφ'(g) |det g|^s Θ(Φ, g) dg`, for `Re s` large. The same
   holds for the dual data `(η⁻¹, φ̃, φ̃', Φ̂)`.
2. `EqualData.main` (module `EqualAnalyticMain`): the right-hand sides equal
   `A(s) + Ã(1 - s) + R(s)` and `Ã(s) + A(1 - s) + R̃(s)`, with `A`, `Ã` entire and bounded in
   strips. `R`, `R̃` are explicit simple fractions, nonzero only if `η = |·|^w`. Hence the poles,
   the strip bounds and the functional equation.

## This module

- `cuspFunction_zeta_mul`: the central character of a cusp form,
  `φ(a g) = ω(a) φ(g)`, from the Library's `centralCharacter_evaluate`.
- `cuspFunction_symm`, `prod_decay_real`, **`pointDecay_cuspFunction_mul`**: the product
  `φ φ'` has chamber decay (`PointDecay`). This follows from the published
  `UnequalAnalytic.hasChamberDecay` for each cusp form.
- `ideleChar_inv_apply`: `χ(a⁻¹) = χ⁻¹(a)`.
- `equalAnalyticStatement_proof`:
  - build `EqualData` from `P = φ φ'`, `χ = ω ω'`, `ψ`, `Φ`, the Siegel decomposition
    `exists_siegelDecomposition`, and the decay;
  - take `σ₀`, `I` and `Ĩ` from `EqualData.main`;
  - for `Re s > σ₀`, apply `equalIntegral_unfold` to `(ω ω', φ, φ', Φ)`, and to
    `(ω ω')⁻¹`, `φ̃ = φ ∘ ι`, `φ̃' = φ' ∘ ι` (`dualFunction_eq`) and `Φ̂`. The dual central
    character follows from `iota_zeta`.

## Supporting modules

All are in `Langlands/Global/RankinSelberg/`, each with its own Markdown:

- `EqualAnalyticExpHom`, `EqualAnalyticFundamentalDomain`, `EqualAnalyticIdeles`,
  `EqualAnalyticIdeleCharacter`, `EqualAnalyticCentralFibration`: the measure theory of the
  centre and the idele class group.
- `EqualAnalyticTheta`, `EqualAnalyticThetaBound`, `EqualAnalyticRationalRows`,
  `EqualAnalyticEisenstein`, `EqualAnalyticEisensteinInvariance`, `EqualAnalyticUnfolding`:
  the Eisenstein series and the unfolding.
- `EqualAnalyticCover`, `EqualAnalyticRegions`: finiteness from Siegel-domain bounds.
- `EqualAnalyticResidue`, `EqualAnalyticDualTransport`, `EqualAnalyticContinuation`,
  `EqualAnalyticIdentification`, `EqualAnalyticPoles`, `EqualAnalyticMain`: the continuation and
  the functional equation.

Poisson summation on `𝔸^n` comes from the published Part A modules
(`EqualAnalyticPoissonGL.hasSum_poisson_mul`).
