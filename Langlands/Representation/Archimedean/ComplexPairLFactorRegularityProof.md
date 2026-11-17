# Proof: right half-plane regularity of complex pair `L`-factors

Author: Worker 3657. Verified and submitted by Worker 831 from the shared Task 6818 draft.

Module `Langlands.Representation.Archimedean.ComplexPairLFactorRegularityProof` proves

```lean
theorem Langlands.Archimedean.complexPairLFactorRightHalfPlaneRegularity :
    ComplexPairLFactorRightHalfPlaneRegularityStatement
```

The target is the published proposition
`Langlands.Archimedean.ComplexPairLFactorRightHalfPlaneRegularityStatement` of module
`Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement`, unchanged:

```lean
∀ (ds ds' : List ComplexCharacterData) (s : ℂ),
  (∀ x ∈ ds, ∀ y ∈ ds', 0 < s.re + x.exponent.re + y.exponent.re) →
    (complexPairLFactor ds ds').denominator s ≠ 0
```

The complex pair `L`-factor `L(s, ds × ds') = 1 / P(s)` has no pole at `s`, that is
`P(s) ≠ 0`, when `Re(s) + Re(t) + Re(t') > 0` for every exponent `t` of `ds` and `t'` of
`ds'`. This is target 2 of Task 6818 (`7825d219-2a04-4194-9e19-95b05a84c4dc`).

The module imports the statement module and the helper
`Langlands.Representation.Archimedean.PairBlockExponent` (paired Markdown beside it). The
theorem uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof follows step 1 of "Why the statements are true" in the statement Markdown.

1. By definition `complexPairLFactor ds ds' = complexLFactor (complexPairBlocks ds ds')`. The
   published `complexLFactor_regular_iff` (module
   `Langlands.LocalFactor.ArchimedeanPresentation`) turns `P(s) ≠ 0` into a condition on the
   poles of the shifted `Γ_ℂ` factors. For every character `d` of the pair presentation and
   every `k : ℕ`, `s + (d.exponent + |d.weight|/2) ≠ −k`.
2. By the helper `mem_complexPairBlocks`, every such `d` is `x.mul y` with `x ∈ ds` and
   `y ∈ ds'`. By `ComplexCharacterData.exponent_mul`, its exponent is
   `x.exponent + y.exponent`.
3. Suppose the equation held. Taking real parts gives
   `Re(s) + Re(x.exponent) + Re(y.exponent) + |m|/2 = −k` with `|m|/2 ≥ 0` and `k ≥ 0`, so
   `Re(s) + Re(x.exponent) + Re(y.exponent) ≤ 0`. This contradicts the hypothesis
   (`linarith`).

## Provenance

The argument is elementary. The poles of `Γ_ℂ(s) = 2 (2π)^(−s) Γ(s)` lie at `s = −k`, `k ∈ ℕ`.
The Library has already proved this as `complexLFactor_regular_iff`, so the proof only adds
the exponent bookkeeping. The complex `L`-factors are the Library's factors of local Langlands
parameters: A. W. Knapp (1994), *Local Langlands correspondence: the archimedean case*,
registered as `knapp-1994-archimedean-llc`, (3.4)–(3.5) and Theorem 2, p.403 (PDF 413), and the complex correspondence
in (4.1)–(4.5), Theorems 4–5, pp.405–406 (PDF 415–416), through the published `StandardModule` and `ArchimedeanPresentation` Markdown. The statement is used in
the reduction of the complex case of J. R. Getz and H. Hahn (2024), *An introduction to
automorphic representations* (`getz-hahn-2024-automorphic-representations`),
Theorem 11.5.2, p.305 (PDF 316).
