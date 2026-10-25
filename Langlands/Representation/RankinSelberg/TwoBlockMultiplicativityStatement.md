# Two-block multiplicativity of the factors of pairs

Author: Worker 358.

This module defines the two-block cases of the published
`GammaMultiplicativityStatement` and `LFactorMultiplicativityStatement`, in
namespace `Langlands.RankinSelberg`. It imports
`Langlands.Representation.RankinSelberg.MultiplicativityStatement` and reuses
its `succBlockShape`, actual canonical normalized induction, and certified
symmetric factor relations. The formulas specialize the published statements
of Worker 11 to `k = 2`; no imported definition is changed.

All three declarations are proposition definitions. This module proves
neither analytic target nor the reduction to an arbitrary number of blocks.

## Original source and reading

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics **105** (1983), 367–464.

- Registered literature ID: `jpss-1983-rankin-selberg`.
- Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- SHA-256:
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Exact locators: §3.1, printed pages 404–405, display (1), display (2),
  and Theorem (3.1)(i)–(ii); §3.2, printed page 405.
  These are PDF pages 39–40, counting the cover as page 1.

The cited pages were read visually from the registered scan and the file hash
was checked. No source-specific erratum was found in the checked project,
Library, or literature errata locations or the literature pointer index.

On page 404 the source takes representations of Whittaker type and induces
the ordered block family from the lower standard parabolic. It recalls
Proposition (2.3) for preservation of Whittaker type, and defines gamma from
epsilon and the L-factors. Page 405 states the gamma product and the inclusion
of the induced L-factor in the product of the block L-factors times
`ℂ[q^(-s), q^s]`. Section 3.2 explains that the case of two blocks implies
the general case by induction on the number of blocks. It places the proof
in Sections 3–7; that proof is not supplied here.

## Quantifiers and hypotheses

Both targets use exactly the telescope of their published counterparts,
with the binder `k` removed and each `Fin k` replaced by `Fin 2`:

- Every prime `p`, every `F : PadicField.{uF} p` with its canonical
  topological data, every `ψ : UnitaryAdditiveCharacter F.Carrier`, and
  every supplied
  `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
  The character type includes continuity, unitarity and nontriviality.
- Every `r t : ℕ`, every `m : Fin 2 → ℕ`, and
  `h : ∑ i, (m i + 1) = t + 1`.
  Thus the first rank is `r + 1`, the induced rank is `t + 1`, and the
  two positive block ranks are `m i + 1`.
- Every complex representation `π` of `GL_(r+1)(F)` on `V : Type uV`
  and every dependent family `σ i` of complex representations of
  `GL_(m i+1)(F)` on `W i : Type uW`.
- The only representation hypotheses are that `π` and each `σ i` satisfy
  `IsOfWhittakerType` for the corresponding `standardCharacter ψ`.
  In particular, reducible inputs are retained.

The universe levels `uF`, `uV` and `uW` remain independent. There is no
inequality between the ranks: `IsPadicSymmetricGammaFactor` and
`IsPadicSymmetricLPolynomial` use the larger rank first, as in the imported
pair-factor convention. The field scope is p-adic, rather than all
nonarchimedean local fields. The statements take a self-dual Haar measure
as data and do not prove its existence.

## Conclusions

`TwoBlockGammaMultiplicativityStatement` asserts the existence of
`G : Fin 2 → RationalFunctions` such that every block pair satisfies
`IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)`, and the pair of `π`
with
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ`
satisfies the same relation at `∏ i, G i`. The witnesses are certified
gamma factors, not arbitrary functions assumed to be factors.

`TwoBlockLFactorMultiplicativityStatement` asserts the existence of
`P : ℂ[X]` and `Pi : Fin 2 → ℂ[X]` certified by
`IsPadicSymmetricLPolynomial` for the induced pair and the block pairs,
respectively, together with `Q : ℂ[X]` and `e : ℕ` satisfying

```text
X ^ e * ∏ i, Pi i = Q * P.
```

To check the direction, write `X = q^(-s)`, the induced L-factor as `1/P`,
and the block L-factors as `1/Pi i`. The source's inclusion says that
`(∏ i, Pi i) / P` is a Laurent polynomial. Clearing its negative powers
of `X` gives precisely the displayed equation. This explanation is not a
formal proof of a Laurent-polynomial equivalence in this module.

`TwoBlockMultiplicativityStatement` is the conjunction of these two
proposition definitions at the same independent universe levels.

Neither factor existence nor Whittaker type of the induced representation
is a premise. Establishing those properties is part of the future proof,
using the actual induction and the existing factor relations.

## Lower and upper parabolics

The source starts with the lower standard parabolic; the imported
`canonicalNormalizedProductInduced` uses the upper standard block
parabolic. Translating the source requires reversing the **entire ordered
block family**: its sizes, dependent carriers and representations. For two
blocks this exchanges the two block positions.

A future proof must construct the conjugation equivalence of the actual
normalized induced representations, respecting their modulus factors and
right actions, then transport the certified factors across that
equivalence. It must also identify the products after reindexing. The
published `IsPadicSymmetricGammaFactor.congr_equiv` and
`IsPadicSymmetricLPolynomial.congr_equiv` provide factor-invariance APIs,
but the required induction equivalence and its application to these
targets are not constructed here. No such equivalence is assumed as a
hypothesis.

Likewise, §3.2 motivates isolating the two-block targets but does not
formally discharge the separate finite-block proof tasks. Normalized
induction transitivity, preservation of Whittaker type, the necessary
coordinate identifications, and the analytic two-block arguments remain
proof obligations outside this statement module.

## Lean verification

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, the module compiled
with no errors or warnings. Separate inspections of both analytic targets
and their conjunction reported `statement_returns_prop: true` and exactly
the level parameters `uF`, `uV`, `uW`. Their inspected assumptions are
`propext`, `Classical.choice` and `Quot.sound`. There are no proof holes or
new axioms. Compilation checks the proposition definitions; it does not
prove them.
