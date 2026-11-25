# Continuity and half-plane integrability of real principal-series matrix coefficients

This module supplies the integrability part of the matrix input
`RealMatrixCoefficientNormalizedGrowth` (from `RealLocalEqualFiniteSquareChambers`) used by the
real equal-rank steps. Notation: `G = GL_{r+1}(ℝ)`, `P` the smooth position principal series of
a real block list `ds`, `π(g)` right translation on `P` (`RealPrincipalSeries.translate`), and `K`
the orthogonal group `unitaryCompact ℝ (r + 1)`.

## Statements

* `RealPrincipalSeries.continuous_translate_coefficient`: let `ℓ` be a complex-linear form on `P`
  with a finite compact derivative bound (`HasCompactDerivativeBound`). Then for every `f` in `P`
  the coefficient `g ↦ ℓ(π(g) f)` is continuous on `G`.
* `norm_charData_zero_character`: the sign character `charData e 0` has modulus one.
* `RealWeightedMatrixIntegrabilityStatement t` (proved by `realWeightedMatrixIntegrability`, with
  the same content as `exists_realWeightedMatrix_integrable`) fixes:
  * a Haar measure `μ` on `H = GL_{t+2}(ℝ)` and a parity `e`;
  * a block list `es` and a linear form `ℓ` on the smooth position principal series of
    `expand es` with a finite compact derivative bound;
  * a standard vector `f` and two square Schwartz tests `Ψ`, `Ψ'`.

  Write `b = realStandardMatrixCoefficient es ℓ f`, so `b(g) = ℓ(π(g) f)`. Then there is a real
  `β` such that for `Re w > β` two integrands are `μ`-integrable:
  * `g ↦ Ψ(g) · sgn(det g)^e |det g|^(w + m/2) · b(g)`, with `m = t + 1`;
  * `g ↦ Ψ'(g) · sgn(det g)^e |det g|^(w + m/2) · b(ιT g)`, where `ιT` is the inverse transpose.

  The weight `sgn(det g)^e |det g|^(w + m/2)` is `realWeightedMatrixTest (charData e 0)`.

## Proofs

Continuity. Write the bound for `ℓ` as `‖ℓ φ‖ ≤ A ∑_i sup_{k ∈ K} |D^{X_i} φ(k)|` for finitely
many right-derivative words `X_i`. Right derivatives are linear on `P`, so for `g` near `g₀`,
`ℓ(π(g) f) - ℓ(π(g₀) f)` is bounded by `A` times the sum, over `i`, of
`sup_{k ∈ K} |D^{X_i}(π(g) f)(k) - D^{X_i}(π(g₀) f)(k)|`. The function
`(g, x) ↦ D^{X_i}(π(g) f)(x)` is jointly continuous (the Library's `continuous_orbitWord`).
Because `K` is compact, `IsCompact.eventually_forall_of_forall_eventually` makes these suprema
small on a neighbourhood of `g₀`.

Integrability. The Library's `compactFunctionalGrowth` gives `N` and `C ≥ 0` with
`|b(g)| ≤ C H(g)^N` for the matrix height `H`. Since `H(ιT g) = H(g)`
(`realMatrixHeight_inverseTranspose`), the same bound holds for `b ∘ ιT`. The functions
`g ↦ sgn(det g)^e b(g)` and `g ↦ sgn(det g)^e b(ιT g)` are continuous, hence measurable, with
the same bound, because the sign character has modulus one. The Library's
`realMatrixInitialConvergence` then gives integrability of `Φ(g) F(g) |det g|^s` for every Haar
measure, for `Re s ≥ (t + 2) + 2N`. For `s = w + m/2`, the integrand equals the weighted
integrand above (`|det g|^s` is written as `exp(s log|det g|)`). So
`β = (t + 2) + 2N - m/2` works.

## Provenance and scope

This is a technical step for Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §4.7,
pp. 30–31. In the proof of Proposition 4.4 the matrix-coefficient zeta integrals converge
absolutely on a right half-plane, by Lemma 3.3, because the coefficients have polynomial
growth. The continuity statement and the integrability statement for the coefficients of
compact-derivative-bounded forms are internal. The module proves no continuation or
functional equation. It covers only the integrability clauses of
`RealMatrixCoefficientNormalizedGrowth`. The Library does not prove its normalized-growth
clause.
