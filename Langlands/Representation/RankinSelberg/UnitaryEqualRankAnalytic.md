# Unitary generic equal-rank integrals on `Re(s) ≥ 1`

Module
`Langlands.Representation.RankinSelberg.UnitaryEqualRankAnalytic`, namespace
`Langlands.RankinSelberg.UnitaryGeneric`. Helper module of the proof of
`UnitaryGenericLPolynomialNonvanishingStatement`
(`UnitaryGenericLPolynomialNonvanishingProof`). It imports
`UnitaryWeightedWhittakerSquare` (a helper module of the same proof), the published
statement module `SquareIntegrableEqualRankAnalyticStatement` (for the integral
definitions), `IntegrandContinuityProof` and `Langlands.Analysis.MellinHalfPlaneProof`.
It changes no published file.

## Main theorem

```lean
theorem unitaryEqualRankAnalytic (F : PadicField.{uF} p) (n : ℕ) : -- canonical topology
    ∀ ψ [IsMulRightInvariant (unipotentHaar F.Carrier n)] μ, IsCompatible … μ →
      ∀ V W (π σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) _),
        IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
        IsAdmissible σ → Representation.IsIrreducible σ → IsUnitarizable σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) f f' Φ,
          (∀ s : ℂ, 1 ≤ s.re →
            EqualRankConverges ψ (normalizedAbsoluteValue …) μ f.val f'.val Φ s) ∧
          DifferentiableOn ℂ (equalRankModelIntegral ψ (normalizedAbsoluteValue …) μ
            π σ ℓ ℓ' f f' Φ) {s : ℂ | 1 < s.re}
```

The equal-rank JPSS integral

`Ψ(s; W, W', Φ) = ∫_{N \ GL_(n+1)} W(g) W'(g) Φ(e_(n+1) g) |det g|^s dg`

of two irreducible admissible unitarizable representations converges absolutely
for `Re(s) ≥ 1` and is holomorphic on `Re(s) > 1`. This is Jacquet–Shalika I,
Proposition (1.5)(i), with holomorphy on the open half-plane added. It assumes
`IsAdmissible` and `IsIrreducible` directly and allows zero functionals.

The module also proves the published statement
`Langlands.RankinSelberg.UnitaryEqualRankConvergenceStatement` (module
`Langlands.Representation.RankinSelberg.EqualRankEulerStatement`; Jacquet–Shalika
I, Proposition (1.5)(i)):

```lean
theorem unitaryEqualRankConvergence : UnitaryEqualRankConvergenceStatement.{uF, uV, uW}
```

Its hypotheses `Whittaker.IsGeneric ψ n π` contain irreducibility and
admissibility; the proof applies the convergence clause of
`unitaryEqualRankAnalytic` and ignores the nonzero-functional hypotheses.

## Other declarations

The following are the private lemmas of the published
`SquareIntegrableEqualRankAnalyticProof`, restated
publicly in this namespace: `sqrtNormTest`, `norm_sqrtNormTest_sq`,
`equalRank_integrand_eq_mellin` (`I_s = I_0 · |det|^s`), `quotientDet_continuous`,
`norm_equalRank_integrand`, `equalRank_converges_of_weighted_squares` and
`equalRank_converges_of_test_weighted_squares` (domination by
`(|W|² + |W'|²)|Φ| |det|^(Re s) / 2`).

`equalRank_holomorphic_of_real_convergence_one`: convergence at every real
`t > 1` gives holomorphy on `Re(s) > 1`. The published Mellin theorem
`Langlands.Analysis.mellinHalfPlane` is applied with shift `κ = -1`, giving
holomorphy of `w ↦ ∫ I_0 |det|^(w+1)` on `Re(w) > 0`; composing with
`s ↦ s - 1` gives the claim.

## Proof of the main theorem

As in `squareIntegrableEqualRankAnalytic`. Measurability comes from the
published `equalRankIntegrandContinuous` (smoothness from admissibility). For
`Re(s) ≥ 1`, the unitary weighted square estimates
(`unitaryWeightedWhittakerSquare`, standard clause for `π`, inverse clause for
`σ`) at `a = Re(s)/2 ≥ 1/2` and the test `sqrtNormTest Φ` dominate the
integrand. Holomorphy then follows from
`equalRank_holomorphic_of_real_convergence_one`.

## Provenance

- Jacquet–Shalika I (registered as
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
  printed page = PDF page + 498): (1.5), definition (1) and Proposition (i),
  p.507 (PDF 9), proof pp.507–508 (PDF 9–10).
- Getz–Hahn (2024), registered as `getz-hahn-2024-automorphic-representations`
  (PDF page = printed + 11 in Chapter 11): Proposition 11.5.1(a), p.304
  (PDF 315), for (11.20).
- The implemented route is the published square-integrable proof (JPSS 1983
  §8.3, pp.448–451) with the unitary square estimates.

## Lean checks

The module and the whole proof build with no errors or warnings; inspection of
`unitaryEqualRankConvergence` reports the axioms `propext`, `Classical.choice`
and `Quot.sound`.
