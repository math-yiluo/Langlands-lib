# Proof: right half-plane regularity of real pair `L`-factors

Module `Langlands.Representation.Archimedean.RealPairLFactorRegularityProof` proves

```lean
theorem Langlands.Archimedean.realPairLFactorRightHalfPlaneRegularity :
    RealPairLFactorRightHalfPlaneRegularityStatement
```

The target is the proposition
`Langlands.Archimedean.RealPairLFactorRightHalfPlaneRegularityStatement` of module
`Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement`:

```lean
∀ (ds ds' : List RealBlock) (s : ℂ),
  (∀ x ∈ ds, ∀ y ∈ ds', 0 < s.re + realBlockExponent x + realBlockExponent y) →
    (realPairLFactor ds ds').denominator s ≠ 0
```

The real pair `L`-factor `L(s, ds × ds') = 1 / P(s)` has no pole at `s`, that is `P(s) ≠ 0`,
when `Re(s) + Re(t) + Re(t') > 0` for every block exponent `t` of `ds` and `t'` of `ds'`.

The module imports the statement module and the helper
`Langlands.Representation.Archimedean.PairBlockExponent` (paired Markdown beside it). The
theorem uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof follows step 1 of "Why the statements are true" in the statement Markdown.

1. By definition `realPairLFactor ds ds' = realLFactor (realPairBlocks ds ds')`. The Library's
   `realLFactor_regular_iff` (module `Langlands.LocalFactor.ArchimedeanPresentation`) turns
   `P(s) ≠ 0` into two conditions.
   - For every character block `character d` of the pair presentation and every `k : ℕ`,
     `s + (d.exponent + d.parity.val) ≠ −2k`. These are the poles of the shifted `Γ_ℝ`
     factor.
   - For every induced block `induced d` and every `k : ℕ`,
     `s + (d.exponent + |d.weight|/2) ≠ −k`. These are the poles of the shifted `Γ_ℂ`
     factor.
2. Let `d` be such a block and suppose the equation holds for some `k`. By the helper
   `exists_realBlockExponent_of_mem_realPairBlocks`, there are `x ∈ ds` and `y ∈ ds'` with
   `Re(d.exponent) = realBlockExponent x + realBlockExponent y`. For a character or induced
   block, `realBlockExponent` is by definition the real part of its exponent.
3. Take real parts of the equation. In the character case this gives
   `Re(s) + Re(d.exponent) + ε = −2k` with `ε = d.parity.val ≥ 0` and `k ≥ 0`. In the induced
   case it gives `Re(s) + Re(d.exponent) + |m|/2 = −k` with `|m|/2 ≥ 0` and `k ≥ 0`. Either
   way `Re(s) + realBlockExponent x + realBlockExponent y ≤ 0`. This contradicts the
   hypothesis for `x` and `y` (`linarith`).

## Provenance

The argument is elementary. The poles of `Γ_ℝ(s) = π^(−s/2) Γ(s/2)` lie at `s = −2k` and those
of `Γ_ℂ(s) = 2 (2π)^(−s) Γ(s)` at `s = −k`, `k ∈ ℕ`. The Library has already proved this as
`realLFactor_regular_iff`, so the proof only adds the exponent bookkeeping. The archimedean
`L`-factors are the Library's factors of local Langlands parameters: A. W. Knapp (1994),
*Local Langlands correspondence: the archimedean case*, registered as
`knapp-1994-archimedean-llc`, (3.4)–(3.5) and Theorem 2, p.403 (PDF 413), through the
`StandardModule` and `ArchimedeanPresentation` Markdown. The statement is used in the
reduction of the real case of J. R. Getz and H. Hahn (2024), *An introduction to automorphic
representations* (`getz-hahn-2024-automorphic-representations`), Theorem 11.5.2, p.305
(PDF 316).
