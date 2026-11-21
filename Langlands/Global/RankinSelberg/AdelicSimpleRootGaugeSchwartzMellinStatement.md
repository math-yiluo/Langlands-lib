# Full-rank Mellin integrability of simple-root gauges with a Schwartz factor

`AdelicSimpleRootGaugeSchwartzMellinStatement.{u}` is an unproved proposition.
For every `F : Type u` with `Field F`, `NumberField F`, and
`CompactSpace (AdeleQuotient F)`, every natural number `r`, and every real
`τ ≥ 0`, it asks for a real `C ≥ 0` such that the lower integral

```
∫⁻ p : WhittakerQuotient F (r + 1),
    Ξ p.out * ‖Φ (lastRow F r p.out)‖ₑ *
      ENNReal.ofReal (detNorm F (r + 1) p.out ^ σ)
  ∂whittakerQuotientMeasure F (r + 1)
```

is finite for every `Ξ` satisfying the published `IsAdelicSimpleRootGauge F r τ Ξ`,
every `Φ ∈ schwartzBruhat F (r + 1)`, and every real `σ > C`. The same threshold
works for all such gauges and all last-row test functions.

The integral is on the actual quotient `N_(r+1)(𝔸_F) \ GL_(r+1)(𝔸_F)` with the
Library's `whittakerQuotientMeasure`, evaluated at the chosen representatives
`p.out`. The determinant factor is the real power of the normalized idelic
absolute value of the determinant. The gauge's diagonal formula depends on
adjacent diagonal ratios. The last-row Schwartz factor supplies decay in the
remaining scalar diagonal coordinate.

This is derived internal infrastructure for `WhittakerSchwartzGaugeStatement`,
motivated by Jacquet and Shalika, *On Euler Products and the Classification
of Automorphic Representations I*, *Amer. J. Math.* 103 (1981), §4.5, printed pp. 550–551
(source `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`).
Page 550 recalls the simple-root gauge bound and introduces the weighted
two-Whittaker integral. Page 551 reduces the justification of unfolding to
absolute convergence of the weighted integral with one Whittaker function
and then invokes gauge majorization. The proposition isolates the corresponding
Mellin integral for the Library's gauge predicate, with uniformity in both the
gauge and the last-row Schwartz–Bruhat function.
