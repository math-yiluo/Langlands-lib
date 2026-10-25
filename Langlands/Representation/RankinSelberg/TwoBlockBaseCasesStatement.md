# Three two-block analytic base cases for the factors of pairs

Author: Worker 393.

This module, in namespace `Langlands.RankinSelberg`, states the three
two-block bases enumerated in JPSS 1983, §7.1, for both gamma
multiplicativity and L-polynomial divisibility. The six declarations and
their conjunction are `Prop`-valued definitions. No analytic base case,
induction equivalence, or reduction to the general theorem is proved here.

## Original source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics **105** (1983), 367–464.

- Registered source ID: `jpss-1983-rankin-selberg`.
- Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- SHA-256:
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Theorem (3.1), printed pages 404–405, displays (1)–(2) and assertions
  (i)–(ii): hypotheses, lower induction, gamma product and L-factor
  inclusion.
- §3.2, printed page 405: reduction to two blocks.
- Section 4, printed pages 406–420: the source case `r ≥ t`.
- §5.1–§5.4, printed pages 420–423: the source case `r = 1`;
  §5.3 treats assertion (ii), and §5.4 treats assertion (i), including
  reducible representations.
- Section 6, printed pages 427–438, especially §6.1 on page 427 and its
  concluding identity on page 438: the source case
  `t = r + 1`, `t₁ = r`, `t₂ = 1`.
- §7.1, printed pages 438–439, cases (1)–(3): explicit enumeration of
  these three bases for both assertions of Theorem (3.1).

The file hash was verified, and printed pages 404–406, 420–423, 427,
438–439 were read visually from the retained scan. The zero-based PDF
index is the printed page minus 366; the one-based PDF page is the printed
page minus 365. No JPSS-specific erratum was found in the checked project
notes, current Library notes, literature pointer index, or literature
filenames. The section ranges above locate future proof obligations;
they are not evidence of a Lean proof.

## Imported targets and common quantifiers

The sole import is the published
`Langlands.Representation.RankinSelberg.MultiplicativityStatement`.
The formulas are restrictions of its `GammaMultiplicativityStatement`
and `LFactorMultiplicativityStatement`, authored by Worker 11, with `k`
fixed to `2` and only the indicated arithmetic hypotheses added.
They use the same two-block conclusions as the published
`TwoBlockGammaMultiplicativityStatement` and
`TwoBlockLFactorMultiplicativityStatement`; those names are not redefined.
The module reuses `succBlockShape`, the actual canonical normalized
induction from `Induction.BlockFactors`, and the certified symmetric
relations from `RankinSelberg.PadicPairFactors`, without modifying them.

Every one of the six targets retains the full quantification over:

- Every prime `p`, every `F : PadicField.{uF} p` with its canonical
  topological data, every nontrivial continuous unitary additive character
  `ψ : UnitaryAdditiveCharacter F.Carrier`, and every supplied
  `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
- Every `r t : ℕ`, `m : Fin 2 → ℕ`, and
  `h : ∑ i, (m i + 1) = t + 1`.
- Every complex representation `π` of `GL_(r+1)(F)` on `V : Type uV`,
  and every dependent block family `σ i` of representations of
  `GL_(m i+1)(F)` on `W i : Type uW`, with the required additive group and
  complex module structures.

The levels `uF`, `uV`, and `uW` are independent. The only representation
hypotheses are the full `IsOfWhittakerType` conditions on `π` and each
`σ i`, for their corresponding `standardCharacter ψ`. This predicate
retains admissibility, finite generation, and a one-dimensional space of
Whittaker functionals. Reducible representations are included.
Whittaker type of the induced representation, irreducibility,
factor existence, analytic identities, and representation transport are
not added as premises.

The scope is the published p-adic specialization of the source, and the
measure is supplied as data. These targets do not assert existence of a
self-dual Haar measure; they retain the full target's quantification over
every such measure.

## Rank conventions and the three restrictions

Source ranks and Lean indices differ by one. If the source ranks are
`R`, `T`, and `T₁, T₂`, then `R = r + 1`, `T = t + 1`, and the upper
block ranks are `m i + 1`.

| Base in §7.1 | Gamma target | L target | Added arithmetic hypotheses |
| --- | --- | --- | --- |
| (1), source `R ≥ T`, Section 4 | `TwoBlockGammaDominantRankStatement` | `TwoBlockLDominantRankStatement` | `t ≤ r` |
| (2), source `T = R + 1`, `T₁ = R`, `T₂ = 1`, Section 6 | `TwoBlockGammaAdjacentRankStatement` | `TwoBlockLAdjacentRankStatement` | `t = r + 1` and `m 0 = 0` |
| (3), source `R = 1`, Section 5 | `TwoBlockGammaRankOneStatement` | `TwoBlockLRankOneStatement` | `r = 0` |

In each target the arithmetic hypotheses precede the two Whittaker-type
hypotheses. The adjacent case has actual induced rank `r + 2`, test rank
`r + 1`, and first upper block rank `1`. The rank sum expands to
`(m 0 + 1) + (m 1 + 1) = t + 1`; with `m 0 = 0` and `t = r + 1` this
gives `m 1 = r`. That equation is a consequence, not an extra premise.
The target does not set `m 1 = 0`.

## Lower-to-upper order and transport

JPSS's display (3.1.1) uses the lower standard parabolic with ordered
blocks `(σ₁, σ₂)` of ranks `(T₁, T₂)`. The Library's
`canonicalNormalizedProductInduced` uses the actual upper standard block
parabolic in the order supplied by `m` and `σ`. Conjugation by a block
antidiagonal permutation changes the source lower parabolic to the upper
parabolic of reversed type. Thus the source lower family
`(σ₁, σ₂)` becomes the upper family `(σ₂, σ₁)`, reversing the sizes,
dependent carriers, and representations together. In particular,
source `T₂ = 1` gives upper `m 0 = 0`.

A future proof must construct the equivalence between these actual
normalized induced representations, with their half-modulus factors
and right translation actions, and transport the certified factors
across it. The published
`IsPadicSymmetricGammaFactor.congr_equiv` and
`IsPadicSymmetricLPolynomial.congr_equiv` supply factor transport once
the representation equivalences have been constructed; reindexing must
also identify the block products. No transport equivalence is assumed or
constructed in this statement module. Commutativity of the factor
product alone does not identify the induced representations.

## Certified conclusions

Each gamma target concludes that there is a family
`G : Fin 2 → RationalFunctions` satisfying
`IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)` for every `i`, and

```text
IsPadicSymmetricGammaFactor F ψ ν.val π
  (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) (∏ i, G i).
```

Each L target concludes that there are `P : ℂ[X]` and
`Pi : Fin 2 → ℂ[X]` satisfying
`IsPadicSymmetricLPolynomial F ψ ν.val π
  (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P`
and `IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)` for every
`i`, with `Q : ℂ[X]` and `e : ℕ` such that

```text
X ^ e * ∏ i, Pi i = Q * P.
```

With `X = q^(-s)`, the certified induced L-factor is `1/P(X)` and the
block L-factors are `1/Pi i(X)`. Theorem (3.1)(ii) says that the induced
L-factor belongs to the product of the block L-factors times the Laurent
polynomial ring. Therefore `(∏ i, Pi i) / P` is a Laurent polynomial;
clearing negative powers yields precisely the displayed equation.
This preserves the source direction. No equivalence with a separate
divisibility predicate is proved here.

The symmetric relations read the pair with the larger rank first and
retain their complete certificates. The gamma relation includes
existence of compatible quotient measure data and nonzero Whittaker
functionals, and its functional equations apply to every compatible
quotient measure and every pair of nonzero functionals. Its equation
certificate includes a nonzero zeta integral. The p-adic L relation
includes existence of compatible quotient measure data and asserts the
normalized ideal-generator relation for every compatible quotient
measure; in particular the certified L-polynomial has constant term
`1`. These witnesses are actual factor certificates for the given
representations. They are not arbitrary numerical factor functions.

`TwoBlockBaseCasesStatement.{uF,uV,uW}` is the conjunction in the order
gamma dominant, L dominant, gamma adjacent, L adjacent, gamma rank one,
L rank one, all at the same three independent levels.

## Lean verification

The module compiled successfully in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings.
All six analytic proposition definitions and their conjunction were
individually inspected with `lean_check`: every inspection reports
`statement_returns_prop: true` and the independent level parameters
`uF`, `uV`, and `uW`. The reported transitive axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. These are statement
checks; they supply no proof of the analytic propositions.
