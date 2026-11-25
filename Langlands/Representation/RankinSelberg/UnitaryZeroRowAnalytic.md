# Unitary generic zero-row integrals on `Re(s) ≥ 1`

Module
`Langlands.Representation.RankinSelberg.UnitaryZeroRowAnalytic`, namespace
`Langlands.RankinSelberg.UnitaryGeneric`. Helper module of the proof of
`UnitaryGenericLPolynomialNonvanishingStatement`
(`UnitaryGenericLPolynomialNonvanishingProof`). It imports
`UnitaryWeightedWhittakerSquare` (a helper module of the same proof) and the
published modules `SquareIntegrableZeroRowAnalyticStatement`,
`ZeroRowLastRowCutoffProof`, `UnequalRankZeroRowIntegrandContinuityProof` and
`Langlands.Analysis.MellinHalfPlaneProof`. It changes no published file.

## Main theorem

```lean
theorem unitaryZeroRowAnalytic (F : PadicField.{uF} p) (n k : ℕ) : -- canonical topology
    ∀ ψ [IsMulRightInvariant (unipotentHaar F.Carrier n)] μ, IsCompatible … μ →
      ∀ (ν : AdditiveHaarMeasure F.Carrier) V W
        (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
        IsAdmissible σ → Representation.IsIrreducible σ → IsUnitarizable σ →
        ∀ ℓ ℓ' f f',
          (∀ s : ℂ, 1 ≤ s.re → UnequalRankConverges ψ (normalizedAbsoluteValue …) 0 k
              μ (rectangularMeasure ν 0 (n + 1)) f.val f'.val s) ∧
          DifferentiableOn ℂ (unequalRankModelIntegral ψ (normalizedAbsoluteValue …) 0 k
              μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f') {s : ℂ | 1 < s.re}
```

The zero-row unequal-rank JPSS integral

`Ψ(s; W, W') = ∫_{N \ GL_(n+1)} W(diag(g, 1_(k+1))) W'(g) |det g|^(s - (k+1)/2) dg`

(Getz–Hahn (11.19), top) of irreducible admissible unitarizable `π` of
`GL_(n+k+2)` and `σ` of `GL_(n+1)` converges absolutely for `Re(s) ≥ 1` and is
holomorphic on `Re(s) > 1`.

## Declarations

The lemmas `zeroRowProductEquiv`, `zeroRow_integrable_iff`,
`zeroRow_converges_iff`, `zeroRow_integral`, `integrable_of_two_square_bounds`,
`norm_zeroRow_integrand_mk`, `zeroRow_integrand_mellin`,
`quotientDeterminantAbs_continuous` and `zeroRow_coefficient_norm_of_cutoff` are
the private lemmas of the published `SquareIntegrableZeroRowAnalyticProof`,
restated publicly. New:

- `integrable_mellin_of_unitary_squares`: if `‖c‖ = u v`,
  `u² d^(-(r-1))` and `v² d^(2 Re s - 1)` are integrable, then
  `c · d^(s - r/2)` is integrable. The split is
  `‖c‖ d^(Re s - r/2) = (u d^(-(r-1)/2)) · (v d^(Re s - 1/2))` with
  `ab ≤ (a² + b²)/2`. The published proof splits as
  `(u d^(-r/2)) · (v d^(Re s))` instead.
- `zeroRow_analytic_of_unitary_square_estimates`: convergence on `Re(s) ≥ 1`
  and holomorphy on `Re(s) > 1` from the restriction estimate with weight
  `|det|^(-k)` and the weighted square for `a ≥ 1/2`. Holomorphy: the published
  Mellin theorem with shift `r/2 - 1`, composed with `s ↦ s - 1`.

## Proof of the main theorem

The published `zeroRowLastRowCutoff` gives a Schwartz–Bruhat `Φ` with
`W(diag(g,1_(k+1))) Φ(lastRow g) = W(diag(g,1_(k+1)))`. With `r = k + 1`:

- `u² d^(-k)` is integrable by `unitaryWhittakerRestriction` (module
  `UnitaryWhittakerRestriction`);
- `v² d^(2 Re s - 1) = |W'|² |Φ|² |det|^(2(Re s - 1/2))` is integrable by the
  inverse clause of `unitaryWeightedWhittakerSquare` at `a = Re s - 1/2 ≥ 1/2`.

`zeroRow_analytic_of_unitary_square_estimates` concludes.

## Provenance

- Getz–Hahn (2024), registered as `getz-hahn-2024-automorphic-representations`
  (PDF page = printed + 11 in Chapter 11): (11.19) and Proposition 11.5.1(a),
  p.304 (PDF 315).
- JPSS 1983 (`jpss-1983-rankin-selberg`), §8.3, restriction estimate (7), p.450,
  and the Cauchy–Schwarz argument, p.451, in the square-integrable case. The
  implemented route is the published proof with the unitary exponents; it is
  internal to the project.

## Lean checks

The module and the whole proof build with no errors or warnings.
