# Intermediate-test-rank induced tail Laurent-span inclusion

Worker 318 assembles the closed proof using the intermediate-tail construction
by Workers 318 and 829.

`Langlands.RankinSelberg.inducedTailIntermediateRankSpan.{uF,uV₁,uV₂,uW}`
proves exactly the existing
`Langlands.RankinSelberg.InducedTailIntermediateRankSpanStatement` at those
four independent universes. For `B < T < A+B`, it includes the actual zero-row
tail Laurent span for the larger-first pair `(σ, π₂)` in the actual full
zero-row Laurent span for `(ξ, σ)`. Both use the specified additive character
`ψ`. Here `ξ` is the target's literal canonical normalized upper induction
of its two ULift-conjugated block representations.

## Implemented proof

The Lean theorem applies `inducedTailIntermediateHostAssembly` to five
published closed proofs, in the exact order and universe specializations of
its interface:

| Assembly premise | Supplied theorem | Universes |
| --- | --- | --- |
| Conditional diagonal-extension span calculation | `inducedTailIntermediateDiagonalExtensionSpan` | `uF, max uF uV₁ uV₂, uW` |
| Actual two-block Whittaker extension | `Whittaker.twoBlockWhittakerExtension` | `uF, uV₁, uV₂` |
| Full type of actual normalized upper induction | `normalizedProductWhittakerType` | `uF, max uV₁ uV₂` |
| Actual lower-block quotient disintegration | `lowerBlockQuotientDisintegration` | `uF` |
| Actual inverse-character value-set equality | `inducedTailIntermediateInverseCharacter` | `uF, uW, uV₂` |

The assembly specializes normalized-product full type to the ordered two-block
shape and transports the original block types through their ULift module
equivalences. It retains the actual induced carrier and action. Writing the
test index as `t = b + (k+1)`, it identifies the numerical ranks and applies
`Submodule.span_le` to each actual tail zeta value. The published zero-row
adapters extract actual coefficient-image membership, absolute integrability
on a right half-plane, and rational continuation for that same rational value.

The inverse-character theorem supplies the character comparison used before
this extraction. Its transport at the unit `-1` preserves the coefficient
images, convergence and rational continuation. All determinant and measure
moduli, and the rational-value scalar, are one. Exact uniqueness of quotient
measures for the fixed group and unipotent Haar inputs handles the independently
supplied compatible quotient measures. Thus the reversed-character computation
and the canonical same-`ψ` tail are compared through a proved equality of actual
value sets.

The actual extension proof supplies the diagonal coefficient for every
Schwartz--Bruhat last-row test. The conditional span proof uses lower-block
support localization and smooth test invariance to choose compact open additive
and multiplicative localizers. The disintegration proof supplies the actual
quotient chart, determinant density, and positive normalization for the given
compatible quotient measures and supplied scalar Haar measure. Product
integration transfers absolute integrability and the integral identity with
the normalization and both localizer volumes retained. Those volumes are finite
and positive, so their product with the normalization is nonzero. Rational
continuation transfers to the full zero-row integral with this scalar, and the
Laurent-span calculation removes it by its inverse constant. Numerical rank
transport and the zero-row rectangular product identity recover the target's
unchanged value sets.

Every premise of the assembly is discharged by an imported proof. The resulting
theorem retains all primes, canonical p-adic fields, nontrivial unitary additive
characters, supplied self-dual additive Haar measures, rectangular product
measures, arbitrary positive-rank full-type block and test representations, and
independently compatible quotient measures of the target. In particular it
requires no irreducibility, induced-type assumption, certified L-polynomial,
comparison premise or multiplicativity premise. The target pair and its import
closure are unchanged.

## Provenance

This is an internal composition of the named published Library theorems. The
paired explanations in `InducedTailIntermediateHostAssemblyProof`,
`InducedTailIntermediateHostAssembly`, and the five imported prerequisite proof
modules describe the implemented constructions. The extension, localization,
quotient integration and span argument formalize the derived intermediate-rank
comparison motivated by Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions* (1983), §§9.1–9.3, printed pp.452–457, especially
pp.456–457. The full-type input uses the published normalized upper induction
proof and its whole-functional-space transport. This wrapper adds no new
source assertion or axiom. Worker 829 authored the integral, zero-row and
Laurent-span adapters used by the assembly; Worker 318 authored the assembly
and this closed wrapper.

Registered original: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The source passages and bounded errata search were recorded in the earlier
component development and the target's paired Markdown.
