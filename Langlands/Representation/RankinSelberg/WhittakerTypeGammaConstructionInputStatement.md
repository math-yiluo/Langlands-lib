# Canonical symmetric gamma construction inputs from Whittaker type

The sole declaration is the proposition definition
`Langlands.RankinSelberg.WhittakerTypeGammaConstructionInputStatement.{uF,uV,uW}`.
It states that standard Whittaker type of both original representations supplies
the existing canonical symmetric gamma construction input. This file supplies
no proof of that proposition.

For every prime `p`, every `F : PadicField.{uF} p`, every
`UnitaryAdditiveCharacter F.Carrier` for the canonical topology, every supplied
`ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`,
every `r n : ℕ`, and actual complex representations `π` and `σ` of
`GL_(r+1)(F)` and `GL_(n+1)(F)` on independently quantified carriers
`V : Type uV` and `W : Type uW`, the statement is

```text
IsOfWhittakerType r (standardCharacter ψ r) π →
IsOfWhittakerType n (standardCharacter ψ n) σ →
PadicSymmetricGammaConstructionInput F ψ ν.val π σ.
```

The character structure includes continuity, unitarity and nontriviality.
`SelfDualHaar` is the existing subtype of actual additive Haar measures satisfying
intrinsic Fourier self-duality. The statement quantifies over supplied witnesses;
it chooses no measure and asserts no self-dual-measure existence theorem.
`IsOfWhittakerType` means admissibility, finite generation over the group algebra,
and a functional space linearly equivalent to `ℂ`. It does not impose
irreducibility or finite dimension on either representation carrier.

All ranks are positive successors, including rank one and equal ranks. There
is no equality constraint between the carrier universes, rank-order premise,
factor-existence premise, or additional analytic premise.

## Source and derived provenance

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.

Printed pages 385–386 (§2.1), 390–391 (Theorem 2.7) and 403 (§2.12)
were read visually (PDF pages 20–21, 25–26 and 38). Section 2.1 defines
Whittaker type, explains replacement of the character by its inverse, and
describes the inverse-transpose representation and transformed model.
Theorem 2.7 gives convergence, rationality, normalized generators, the common
unequal-rank generator, and the functional equations; it explicitly includes
the inverse-transpose pair. Section 2.12 supplies the convention of placing
the larger rank first. No separate erratum note for this source was present
in the checked project or Library `notes/errata` locations.

This proposition is derived packaging in the Library's canonical p-adic
interfaces, not a verbatim theorem of the article. Its provenance is the cited
JPSS results together with the existing definitions in
`GammaFromWhittakerType`, `PadicGammaFactor`, `AnalyticStatement`,
`FunctionalEquationStatement`, and `LocalFactor.Abelian.Padic`.
It claims no proof of the cited results.

## Exact retained input and proof obligations

`PadicSymmetricGammaConstructionInput` is reused unchanged. If `n ≤ r`,
it is `PadicPairGammaConstructionInput F ψ ν.val π σ`; otherwise it is
`PadicPairGammaConstructionInput F ψ ν.val σ π`. Equal rank uses the first
branch. This convention by itself proves no rank-exchange identity.

For an ordered pair `(ρ, τ)` of ranks `R+1 ≥ N+1`, the reused predicate installs
the canonical topology, valuation, local-field and Borel structures, residue
cardinality `q`, `normalizedAbsoluteValue F.canonicalTopologicalData`, and
the actual quotient measure `unipotentQuotientHaar F.Carrier N`. It retains
the rank inequality, self-duality of `ν.val`, `PairEpsilonFactorExists`,
standard type of `ρ`, inverse-standard type of `τ`, and both original and
dual `PairAnalyticInput` propositions. No bespoke replacement predicate or
factor constructor is introduced.

The following obligations remain for a proof of the closed statement.

1. **Original character transport.** Both premises use `standardCharacter ψ`.
   The second representation in the ordered branch must have
   `inverseStandardCharacter ψ` type as well. The published
   `Langlands.Whittaker.characterChangeFunctionalEquiv` at the unit `-1`,
   with `standardCharacter_scale_neg_one`, provides the functional-space
   transport. Admissibility and finite generation concern the same
   representation and remain unchanged. Packaging these facts into full
   `IsOfWhittakerType` transport is a proof step, not a premise or a theorem
   supplied here. In the reversed branch this step applies to the original
   `π`, which is then second.

2. **Original and dual analytic conclusions.** `PairAnalyticInput` quantifies
   over every pair of nonzero functionals. In equal rank it requires
   `EqualRankAnalyticConclusion`, including every Schwartz–Bruhat test.
   In unequal rank it requires `UnequalRankAnalyticAt` for every admissible
   rectangular block. These include convergence, rational continuation,
   common denominators and normalized-generator existence. Both the original
   ordered pair at `ψ` and its actual `inverseTransposePullback` pair at
   `ψ.scale (-1)` must satisfy these conclusions, using the same scalar Haar
   measure and canonical quotient measure. Original analyticity alone does
   not supply the dual input.

3. **Dual type.** The published `isOfWhittakerType_firstDual` and
   `isOfWhittakerType_secondDual` in `GammaFromWhittakerType` supply the
   respective standard and inverse-standard types for the pullback pair at
   `ψ.scale (-1)`, after the original second-character transport.
   Their underlying theorems are in `DualWhittakerType`. These are actual
   inverse-transpose pullbacks; no identification with a smooth
   contragredient is assumed.

4. **Common unequal-rank generator.** The JPSS route includes
   `UnequalRankCommonGeneratorStatement`, for the original and dual families,
   not merely a separate polynomial for each block. It is not an extra
   conjunct added to `PairAnalyticInput`: that predicate is blockwise.
   The common-generator result supports the uniform L-polynomial and
   functional-equation assembly; the unequal-rank functional-equation
   conclusion itself also specifies polynomials uniform in the block.
   The existing conditional bridge
   `UnequalRankCommonGeneratorStatement.pairLPolynomialExists` does not
   prove this substantive generator theorem.

5. **Epsilon existence from functional equations.**
   `PairEpsilonFactorExists` means that a single pair `(c, m) : ℂˣ × ℤ`
   satisfies `IsPairEpsilonFactor`. Its relation includes nonzero-functional
   existence, compatible quotient-measure existence, and the fixed epsilon
   monomial equation for every compatible quotient measure and every
   nonzero functional pair. Thus obtaining constants for one selected
   functional pair is insufficient. A proof must assemble the equal- or
   unequal-rank functional-equation result with the requisite independence
   of functionals and measure; unequal rank also retains uniformity in
   the rectangular block. The normalized equations preserve their central
   sign, Fourier tests in equal rank, and complementary dual block in
   unequal rank. None of this follows merely from `pairEpsilonFactor`,
   which takes epsilon existence as input.

6. **Measures and the inverse character.** The canonical quotient measure
   and its compatibility are already constructed in `UnipotentQuotient`,
   including `unipotentQuotientHaar_isCompatible`; right invariance is
   supplied by `unipotentHaar_isMulRightInvariant`. These results do not
   prove analyticity or a functional equation. The supplied `ν.property`
   gives self-duality for `ψ`. Any use of a self-dual-normalized theorem at
   `ψ.scale (-1)` with this same measure must establish
   `IsSelfDual (ψ.scale (-1)) ν.val`. No such packaged negated-character
   lemma was found in the checked Library, and it is not assumed here.
   The direct analytic statements themselves allow arbitrary additive Haar
   measures, so reusing `ν.val` for their dual instances does not require
   that extra transport. A proof route invoking a dual functional equation
   must discharge it.

## Existing ownership and scope

The substantive proof owners are the existing tasks:

| Published statement | Existing proof task |
| --- | --- |
| `EqualRankAnalyticStatement` | `5998b0b2-e367-4e85-8d4d-47e3b9b4a222` |
| `UnequalRankAnalyticStatement` | `b01bbdd0-5321-41f4-908e-2048e837da34` |
| `UnequalRankCommonGeneratorStatement` | `13326f3a-e77f-4ed1-a44a-b6407f6b7c0a` |
| `EqualRankFunctionalEquationStatement` | `fc96b553-9980-45e3-90d0-641e62ad7a5e` |
| `UnequalRankFunctionalEquationStatement` | `9a87301f-3d9f-4d04-af2a-840798b82af5` |

These task assignments are not proof evidence. Worker 11 owns the source
statement interfaces; Worker 31 owns the existing factor-construction
interfaces. Worker 40 will arrange the separate proof successor of this
closed proposition, including the two character-transport obligations as
needed, without duplicating those five substantive proof tasks.

Worker 46's symmetric L-polynomial existence statement task
`7a757d52-b76b-4a3f-98d8-b258d348bb8b` and Worker 40's consumer
`0153deb3-0833-4025-b869-95be58117eb7` retain their scopes. The separate
conditional `SymmetricGammaExpressionStatement` and
`EqualRankFactorSwapStatement` are not asserted here. Once this proposition
is proved, the existing `padicSymmetricGammaFactorOfWhittakerType` can consume
its conclusion; this module neither constructs that factor anew nor proves
its expression, symmetry, or any analytic theorem.
