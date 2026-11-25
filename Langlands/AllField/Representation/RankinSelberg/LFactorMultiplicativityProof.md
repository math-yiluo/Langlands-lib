# L-polynomial divisibility under normalized block induction, every local field

Module `Langlands.AllField.Representation.RankinSelberg.LFactorMultiplicativityProof`.

`Langlands.AllField.RankinSelberg.lFactorMultiplicativity` proves
`Langlands.AllField.RankinSelberg.LFactorMultiplicativityStatement.{uF, uV, uW}`
(module `Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement`)
with no additional premises. This is the all-field port of the Library's p-adic
statement `Langlands.RankinSelberg.LFactorMultiplicativityStatement`: JPSS 1983,
Theorem (3.1)(ii), for the normalized induction
`(⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ` of any
ordered family of blocks `σ i` of `GL_(m i + 1)(F)`, `i : Fin k`, with
`h : ∑ i, (m i + 1) = t + 1`. For `π` of `GL_(r+1)(F)` and the `σ i` of Whittaker type, it
gives the L-polynomial `P` of `π` against the induced representation, the
L-polynomials `Pi i` of the pairs `(π, σ i)`, all with their full symmetric
certificates `IsPadicSymmetricLPolynomial F ψ ν.val`, and `Q : ℂ[X]`, `e : ℕ` with

```text
X ^ e * ∏ i, Pi i = Q * P.
```

The field `F` is any field with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`, so every nonarchimedean local field is covered,
including those of positive characteristic.

## Proof

This module is the all-field port of the Library module
`Langlands.Representation.RankinSelberg.LFactorMultiplicativityProof` (its Markdown
explains the proof and its provenance). It rests on the all-field two-block theorem,
proved in [TwoBlockLFactorMultiplicativityProof](TwoBlockLFactorMultiplicativityProof.md).

The proof is that of the original: the finite assembler
`lFactorMultiplicativity_of_twoBlock` (all-field module `FiniteLFactorMultiplicativity`),
which reduces any ordered block family to two blocks by
induction in stages, applied to
`twoBlockLFactorMultiplicativity.{uF, uV, max uF uW}`. The universe `max uF uW` is that
of the carrier of the induced tail.

## Source

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983),
registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, Theorem (3.1)(ii),
printed pages 404-405, and Section 3.2 (reduction to two blocks). Section 0.3 (printed
page 375) allows any nonarchimedean local field. With `L = 1/P` and block factors
`1/Pi i`, the displayed equation is the source's membership
`L(s, π × σ) ∈ ∏ L(s, π × σ_i) ℂ[q^(-s), q^s]` after clearing a power of `X`. The
Markdown of the original module gives the full provenance.
