# Proof: entire normalizations of the ordinary complex Rankin–Selberg integrals

Module `Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedContinuationProof`. The theorem

```lean
theorem Langlands.Global.RankinSelbergGlobal.complexOrdinaryNormalizedContinuation :
    ComplexOrdinaryNormalizedContinuationStatement
```

proves `ComplexOrdinaryNormalizedContinuationStatement` (module
`ArchimedeanOrdinaryNormalizedTests`; the statement has no universe parameter). Unfolded, the
statement is

```lean
(∀ (r t : ℕ) (h : t < r) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t),
    HasEntireOrdinaryNormalizations (complexOrdinaryUnequalTest h d e a D)
      (complexPairLFactor d e)) ∧
∀ (r : ℕ) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r),
    HasEntireOrdinaryNormalizations (complexOrdinaryEqualTest r d e a D) (complexPairLFactor d e)
```

In words: for lists `d`, `e` of complex characters of lengths `r + 1` and `t + 1` with `t < r`,
every `a ∈ ℂˣ` and every compatible quotient measure `D`, every test (a pair of vectors of
the Whittaker models `complexWhittakerModel r d a` and `complexWhittakerModel t e (-a)`) has an
entire normalization by `complexPairLFactor d e`: an entire function whose product with the
reciprocal of the denominator of the pair factor agrees with the ordinary integral on a right
half-plane (`OrdinaryIntegralNormalization`). The same holds in equal rank `r = t` for tests that
also include a Schwartz function on `ℂ^(r+1)`.

## Proof as implemented

`complexOrdinaryNormalizedAllGrowth` (module `ComplexOrdinaryNormalizedAllGrowth`) proves
`ComplexOrdinaryNormalizedAllGrowthStatement`, which is by definition the conjunction
`ComplexOrdinaryNormalizedContinuationStatement ∧
CuspidalPairPoles.ComplexOrdinaryNormalizedStripGrowthStatement`. The theorem here is its first
component, `complexOrdinaryNormalizedAllGrowth.1`.

## Declarations

- `complexOrdinaryNormalizedContinuation : ComplexOrdinaryNormalizedContinuationStatement`
  (theorem).

## Provenance

H. Jacquet, *Archimedean Rankin–Selberg integrals*, in D. Ginzburg, E. Lapid and D. Soudry
(eds.), *Automorphic Forms and L-functions II. Local Aspects*, Contemp. Math. 489 (2009), 57–172.
The page below is that of the proceedings volume (file `Part II - Local Aspects.pdf`, PDF page =
printed page + 22); the page of `ArchimedeanOrdinaryNormalizedTests` cites the same theorem in the
registered author's version `jacquet-2009-archimedean-rankin-selberg`, whose pagination differs.
Theorem 2.1(ii), printed p. 62 (PDF page 84): each of the integrals (2.4)–(2.6) "extends to a
meromorphic function of `s` which is a holomorphic multiple of `L(s, σ_u ⊗ σ'_u')`". The
statement here is the ordinary case of (ii) at a complex place for the Library's Whittaker models:
the quotient of the integral by the pair `L`-factor extends to an entire function.
