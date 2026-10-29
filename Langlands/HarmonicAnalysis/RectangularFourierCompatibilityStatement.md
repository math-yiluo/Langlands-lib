# Full rectangular Schwartz Fourier equivalence and reflection

Worker 753 authored this statement for task
`d8f394b0-0444-46c4-ab1f-12fe9f99254c`, published by Worker 486 as a shared
Fourier prerequisite for the adjacent-rank gamma/L work. It is a statement only;
it supplies no proof.

## The proposition

`Langlands.HarmonicAnalysis.RectangularFourierCompatibilityStatement.{uK}` is a
closed proposition definition. Write `M` here only as a prose abbreviation for
the actual type `Matrix (Fin r) (Fin s) K`. The proposition quantifies over an
implicit `K : Type uK` with exactly the instances

```text
[Field K] [TopologicalSpace K] [IsTopologicalRing K]
[MeasurableSpace K] [BorelSpace K]
[LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
```

and over every `ψ : UnitaryAdditiveCharacter K`, every supplied
`μ : AdditiveHaarMeasure K`, and all `r s : ℕ`. Its only premise is
`IsSelfDual ψ μ`. Its conclusion is that there exists an actual complex-linear
equivalence

```text
T : SchwartzBruhat M ≃ₗ[ℂ] SchwartzBruhat M
```

such that all four of the following hold, each for every
`Φ : SchwartzBruhat M` and `b : M`:

1. `T Φ b = rectangularFourierIntegral ψ μ Φ b`;
2. `T.symm Φ b = rectangularFourierIntegral ψ μ Φ (-b)`;
3. `T (T Φ) b = Φ (-b)`;
4. `fun a => Φ a * ψ.complex (rectangularPairing a b)` is
   `MeasureTheory.Integrable` with respect to
   `Langlands.RankinSelberg.rectangularMeasure μ r s`.

Here `T Φ b` evaluates the Schwartz–Bruhat function `T Φ` at `b`, and
`-b` is entrywise negation of the matrix.

## The imported objects

All objects are the published ones, imported unchanged from
[`Langlands.HarmonicAnalysis.RectangularFourier`](RectangularFourier.md) and
its imports; no transform, pairing, measure or test space is introduced here.

- `rectangularPairing a b` is `∑ i, ∑ j, a i j * b i j`, with no sign and no
  conjugation.
- `rectangularFourierIntegral ψ μ f b` is the raw Bochner integral
  `∫ a, f a * ψ.complex (rectangularPairing a b) ∂rectangularMeasure μ r s`
  into all complex functions.
- `Langlands.RankinSelberg.rectangularMeasure μ r s` is the nested finite
  product `Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin s => μ.measure))`
  of the supplied scalar measure. The statement uses this measure itself, not a
  fresh Haar measure, a further normalization, or a pushforward along a
  flattening of the matrix coordinates.
- `SchwartzBruhat M` is the space of locally constant compactly supported
  complex functions for Mathlib's product topology on matrices. The matrix
  measurable structure is Mathlib's product structure induced from `K`.
- `IsSelfDual ψ μ` from [`Langlands.HarmonicAnalysis.Basic`](Basic.md) is
  scalar self-duality: for every scalar test function the second plus-sign
  Fourier integral converges and Fourier squared is reflection.

## What the conclusion contains

The codomain of `T` consists of actual Schwartz–Bruhat functions, so the first
conjunct asserts preservation of the test space by the plus-sign full Fourier
integral. Since a Schwartz–Bruhat function is determined by its values, the
first conjunct determines `T`; the existential does not choose an arbitrary
transform. The linear equivalence contains both inverse laws.

The second conjunct identifies the inverse. Because
`rectangularPairing a (-b) = -rectangularPairing a b`, the integral at the
reflected output is the inverse-character transform
`∫ a, Φ a * ψ.complex (-rectangularPairing a b)`. It is stated through the same
plus integral, so no second raw-transform primitive is introduced. The third
conjunct is the reflection law: Fourier squared equals `Φ ↦ Φ (- ·)`.

The fourth conjunct asserts convergence of the Fourier integrand of every
Schwartz input at every output point. It therefore applies also to `T Φ` and
`T.symm Φ`, and at reflected points `-b`, so every iterated integral appearing
in the first three conjuncts converges.

The cases `r = 0` and `s = 0` are included. Then `M` has exactly one point and
the measure is the unit point mass, so the first conjunct forces `T` to be the
identity.

## Hypotheses not assumed

The proposition adds no premise of scalar or product sigma-finiteness, no
Borel compatibility on a row or matrix product, no second countability, no
continuity of field inversion, no valuation or p-adic structure, no Fourier
closure or inversion, no supplied equivalence, and no additional scalar measure
normalization. A proof must derive any such ingredient from the displayed
hypotheses and published results. For example, the published
`scalarFourierClosure` derives scalar sigma-finiteness and scalar Fourier
closure from `IsSelfDual ψ μ`, and the published `rowFourierCompatibility`
derives row closure and reflection in every finite dimension, both under the
same scalar hypotheses. Any comparison between the nested matrix measure and
a flattened row measure must be proved; a coordinate bijection alone does not
transport the measure.

## Source and provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg` and retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`
with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 753 read Section 6.1 on printed pages 427–428 (one-based PDF pages
62–63) from rendered page images; the scan has no text layer.

On page 427 the source sets `t = r + 1` and works with Schwartz functions on
the `(t - 1) × t` matrices, with the action `(gΦ)(m) = Φ(mg)`. Page 428,
formula (6), defines "the usual Fourier transform"

`Φ^(x) = ∫ Φ(y) ψ(tr(y ᵗx)) dy`,

with a plus sign. Since `tr(y ᵗx) = ∑ i, ∑ j, y i j * x i j`, this is
`rectangularFourierIntegral` with integration variable `a = y` and output
`b = x`. The page then states a covariance law for this transform under the
action of `g` and, using that it commutes with the last-column partial
transform `Φ~` of page 427, `(Φ~)^ = (Φ^)~`, derives formula (7). These pages display no measure normalization for `dy`; the present statement
uses the product of the supplied scalar measure, and scalar self-duality is the
normalization under which Fourier squared is reflection.

No errata for this source were found: there is no
`notes/errata/jpss-1983-rankin-selberg.md` in the workspace, the current
Library or the shared project notes, and the literature index records no
correction for this article.

The statement is an internal derived interface supporting the source's Fourier
construction, not a transcription of a displayed JPSS theorem. On these pages
JPSS treat `Φ^` as a Schwartz function (formula (7) applies `ρ₀` to it) and do
not state preservation, inversion or convergence as separate results. Arbitrary rectangular ranks `r` and
`s`, the generic topological-field hypotheses in place of a p-adic field, the
zero-dimensional cases, the packaging as an explicit linear equivalence with
its inverse formula, and the explicit convergence conjunct are all derived
packaging. The source's adjacent-rank matrix space is the specialization
`r = n`, `s = n + 1` (with `n = t - 1`); the same interface also covers square
matrix spaces `r = s = n`.

## Scope

This unit supplies no proof of closure or inversion, no chosen Fourier
primitive, no covariance law such as formula (7), no Fourier-conjugated action
`ρ₀`, no matrix-zeta definition or comparison, and no gamma or L-factor
analytic base. It edits no existing Lean/Markdown pair.
