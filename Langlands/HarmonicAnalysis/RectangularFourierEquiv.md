# The chosen full rectangular Schwartz Fourier equivalence

This module fixes one complex-linear Fourier equivalence of rectangular
Schwartz–Bruhat functions. It also exposes its forward, inverse, square and
convergence evaluations, and proves that any equivalence with the same forward
values equals it.

## Definition

`Langlands.HarmonicAnalysis.rectangularFourierEquiv.{uK}` takes the following
arguments:

- an implicit carrier `K : Type uK`;
- the eight typeclass hypotheses `[Field K] [TopologicalSpace K]
  [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]`;
- an explicit unitary additive character `ψ`, an explicit additive Haar
  measure `μ`, and explicit natural ranks `r s`;
- an explicit proof `hsd : IsSelfDual ψ μ`.

These are exactly the binders of the published
[`RectangularFourierCompatibilityStatement`](RectangularFourierCompatibilityStatement.md),
in the same order. Its type is

```text
SchwartzBruhat (Matrix (Fin r) (Fin s) K) ≃ₗ[ℂ]
  SchwartzBruhat (Matrix (Fin r) (Fin s) K).
```

Its value is

```text
Classical.choose (rectangularFourierCompatibility ψ μ r s hsd),
```

which is the witness of the existential conclusion of the published theorem
[`rectangularFourierCompatibility`](RectangularFourierCompatibilityProof.md).
The definition adds no premise to that theorem. In particular it adds no
product-space `BorelSpace` or sigma-finiteness instance, no
second-countability or inversion-continuity assumption, and no valuation,
p-adic-field or nonzero-rank restriction. It also introduces no new pairing,
test space or measure. Both empty ranks `r = 0` and `s = 0` are included,
because the theorem covers them.

## Evaluation lemmas

Each of the first four lemmas holds for every Schwartz input `Φ` and every
output matrix `b`. Each is one projection of
`Classical.choose_spec (rectangularFourierCompatibility ψ μ r s hsd)`, taken
in the order of the statement's conjunction.

- `rectangularFourierEquiv_apply`:
  `rectangularFourierEquiv ψ μ r s hsd Φ b =
  rectangularFourierIntegral ψ μ Φ b`.
- `rectangularFourierEquiv_symm_apply`:
  `(rectangularFourierEquiv ψ μ r s hsd).symm Φ b =
  rectangularFourierIntegral ψ μ Φ (-b)`.
- `rectangularFourierEquiv_apply_apply`: applying the equivalence twice to
  `Φ` gives the function whose value at `b` is `Φ (-b)`.
- `rectangularFourierEquiv_integrable`: the integrand
  `fun a => Φ a * ψ.complex (rectangularPairing a b)` is `Integrable` against
  `RankinSelberg.rectangularMeasure μ r s`. This conclusion does not mention
  the equivalence, so the lemma takes `hsd` explicitly through `include hsd in`.

Here `rectangularFourierIntegral ψ μ Φ b` is the published raw integral
`∫ a, Φ a * ψ.complex (rectangularPairing a b)` against
`RankinSelberg.rectangularMeasure μ r s`. That measure is the nested product
`Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin s => μ.measure))`.
The pairing `rectangularPairing a b = ∑ i, ∑ j, a i j * b i j` is the unsigned
entry pairing. The lemmas therefore keep the plus sign of the character, the
unsigned pairing and the actual nested product measure of the theorem
unchanged.

## Uniqueness

`rectangularFourierEquiv_unique` assumes a complex-linear equivalence `T` of
the same Schwartz space with
`T Φ b = rectangularFourierIntegral ψ μ Φ b` for all `Φ` and `b`. It proves
`T = rectangularFourierEquiv ψ μ r s hsd`. The proof uses `LinearEquiv.ext`
and then `Hecke.TestFunction.ext` for the underlying functions, and compares
both values with the raw integral through `rectangularFourierEquiv_apply`.
This is propositional equality obtained from extensionality, not
definitional equality. Because of it, later formulas stated with
`rectangularFourierEquiv` do not depend on which existential witness was
chosen.

## Provenance and scope

The definition and its API are derived internal packaging of the published
full Fourier theorem `rectangularFourierCompatibility`. That theorem proves
the closed statement `RectangularFourierCompatibilityStatement`. The
existential witness is chosen with `Classical.choose`. Every lemma is a
projection of `Classical.choose_spec`, or follows from one by
extensionality. No new analytic statement is assumed or proved here. The
compiled module uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The Fourier convention is inherited unchanged from
[`RectangularFourier`](RectangularFourier.md) and the theorem. The source is
H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. 105 (1983), 367–464, Section 6.1, printed
pages 427–428. The plus-sign full Fourier transform is formula (6) on page
428 (one-based PDF page 63). The registered source is
`jpss-1983-rankin-selberg`, with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. JPSS
does not state a chosen equivalence or these Lean lemmas as separate results.
Formula (6) on the scanned page 428 was checked visually. It reads
`Φ^(x) = ∫ Φ(y) ψ(tr(y ᵗx)) dy`, and `tr(y ᵗx) = ∑ i, ∑ j, y i j * x i j`. This
is the published `rectangularFourierIntegral ψ μ Φ x`, with integration
variable `a = y`. The published `RectangularFourier` Markdown records the same
comparison. No source-specific errata note for this source was found in the
current Library or the shared project notes.

This module contains no covariance statement or proof, no partial Fourier
equivalence, no conjugated `ρ₀` action, no matrix-zeta functional equation,
and no gamma or L-factor analytic base. It does not contain the
square-matrix or Whittaker analytic definitions and comparisons of JPSS
Sections 5.2 and 5.4. The square case is the specialization `r = s = n`.
