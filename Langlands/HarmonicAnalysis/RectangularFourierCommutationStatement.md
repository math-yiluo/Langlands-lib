# Commutation of the full and partial rectangular Fourier transforms

Worker 1037 authored this statement for task
`07f67d15-60b1-4cd0-b29b-b2bfb6c9cfd5`. Worker 486 published that task as a
focused statement successor under the adjacent-rank gamma/L parent
`b54b4d62-d794-49e6-92ef-2838db2b7f47`. The module states that two published
chosen maps commute: the full rectangular Fourier equivalence and the
last-column partial Fourier equivalence. It supplies no proof. Its
exact-target proof is a separate later unit.

## The proposition

`Langlands.HarmonicAnalysis.RectangularFourierCommutationStatement.{uK}` is a
closed proposition definition. Write `M` here only as a prose abbreviation for
the actual type `Matrix (Fin n) (Fin (n + 1)) K`. The proposition quantifies
over an implicit `K : Type uK` with exactly the instances

```text
[Field K] [TopologicalSpace K] [IsTopologicalRing K]
[MeasurableSpace K] [BorelSpace K]
[LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
```

and then, in this order, over every `ψ : UnitaryAdditiveCharacter K`, every
supplied `μ : AdditiveHaarMeasure K`, every rank `n : ℕ`, every proof
`hsd : IsSelfDual ψ μ` and every `Φ : SchwartzBruhat M`. Its body is the
equality of actual Schwartz–Bruhat functions

```text
rectangularFourierEquiv ψ μ n (n + 1) hsd (partialFourierEquiv ψ μ n hsd Φ) =
  partialFourierEquiv ψ μ n hsd (rectangularFourierEquiv ψ μ n (n + 1) hsd Φ).
```

Write `F = rectangularFourierEquiv ψ μ n (n + 1) hsd` and
`T = partialFourierEquiv ψ μ n hsd`. Both are complex-linear equivalences of
the same space `SchwartzBruhat M`, so the body is `F (T Φ) = T (F Φ)`. The
full map is taken at the ranks `r = n` and `s = n + 1`, which gives exactly
this space; no transport between types is involved. Both maps receive the
same character `ψ`, the same measure `μ` and the same proof `hsd`.

Evaluating at an output matrix `b : M`, the equality entails
`F (T Φ) b = T (F Φ) b`. By `rectangularFourierEquiv_apply` and
`partialFourierEquiv_apply`, this is the identity of raw integrals

```text
rectangularFourierIntegral ψ μ (T Φ) b =
  partialFourierIntegral ψ μ (F Φ) b.
```

Here the left side is
`∫ a, (T Φ) a * ψ.complex (rectangularPairing a b)` against
`RankinSelberg.rectangularMeasure μ n (n + 1)`, and the right side is
`∫ u, (F Φ) (rectangularJoin (rectangularFirstColumns b) u) *
ψ.complex (-rowPairing (rectangularLastColumn b) u)` against
`rowMeasure μ n`. A private development check confirmed that the
proposition implies this pointwise identity by these two rewrites alone.

## The imported objects

All objects are published ones, imported unchanged by Lean name. The module
introduces no transform, pairing, measure, test space or action.

- `rectangularFourierEquiv ψ μ r s hsd` from
  [`Langlands.HarmonicAnalysis.RectangularFourierEquiv`](RectangularFourierEquiv.md)
  is the chosen complex-linear equivalence of rectangular Schwartz–Bruhat
  functions. Its forward value `rectangularFourierEquiv_apply` is
  `rectangularFourierIntegral ψ μ Φ b`, the plus-sign integral
  `∫ a, Φ a * ψ.complex (rectangularPairing a b)` against
  `Langlands.RankinSelberg.rectangularMeasure μ r s`.
- `rectangularPairing a b` is the unsigned entry pairing
  `∑ i, ∑ j, a i j * b i j`, with no conjugation.
- `Langlands.RankinSelberg.rectangularMeasure μ r s` is the nested finite
  product `Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin s => μ.measure))`
  of the supplied scalar measure. It is not a fresh Haar measure or a
  pushforward along a flattening.
- `partialFourierEquiv ψ μ n hsd` from
  [`Langlands.HarmonicAnalysis.PartialFourierEquiv`](PartialFourierEquiv.md)
  is the chosen complex-linear equivalence of `SchwartzBruhat M`. Its forward
  value `partialFourierEquiv_apply` is `partialFourierIntegral ψ μ Φ m`, the
  inverse-character last-column integral
  `∫ u, Φ (rectangularJoin (rectangularFirstColumns m) u) *
  ψ.complex (-rowPairing (rectangularLastColumn m) u)` against
  `rowMeasure μ n`. Its explicit self-duality argument is named `hself` in
  that module; the statement passes `hsd` to it.
- `rectangularFirstColumns m` is the square block `fun i j => m i j.castSucc`
  of the first `n` columns, `rectangularLastColumn m` is the last column
  `fun i => m i (Fin.last n)`, and `rectangularJoin x y` is the matrix `[x, y]`
  with first block `x` and last column `y`. All three are from
  [`Langlands.HarmonicAnalysis.RectangularFourier`](RectangularFourier.md).
- `rowPairing x y = ∑ i, x i * y i` is the unsigned row pairing, and
  `rowMeasure μ n = Measure.pi (fun _ : Fin n => μ.measure)` is the finite
  product of the supplied scalar measure, both from
  [`Langlands.HarmonicAnalysis.RowFourier`](RowFourier.md).
- `IsSelfDual ψ μ` from [`Langlands.HarmonicAnalysis.Basic`](Basic.md) is the
  scalar self-duality of `μ` for `ψ`: for every scalar Schwartz–Bruhat `f`,
  the second Fourier integrand converges and the Fourier transform applied
  twice gives `x ↦ f (-x)`.

By `rectangularFourierEquiv_unique` and `partialFourierEquiv_unique`, any
complex-linear equivalences with the same forward evaluations equal the chosen
ones. The proposition therefore does not depend on which existential
witnesses were chosen.

## Why the identity is expected

This section explains the expected mathematics. It is not part of the Lean
statement, and nothing in it is proved here. Split matrices in `M` as
`[x, y]`, with `x` the first `n` columns and `y` the last column. For
`b = [x', y']`, both sides should equal the plus-sign Fourier transform in
the first `n` columns only:

```text
∫ Φ [a₁, y'] ψ (⟨a₁, x'⟩) da₁.
```

On the left, the last-column part of the plus-sign full integral undoes the
inverse-character partial transform, by Fourier inversion on `Kⁿ`. On the
right, the inverse-character partial transform undoes the last-column part
of the full integral, again by Fourier inversion.

A proof must establish every step for the actual measures. It must split the
nested measure `rectangularMeasure μ n (n + 1)` into a measure of the first
`n` columns and the measure `rowMeasure μ n` of the last column, as an
actual equality of measures or integrals. It must justify each exchange of
iterated integrals, and derive Fourier inversion for `rowMeasure μ n` from
the scalar hypothesis `IsSelfDual ψ μ`. A coordinate bijection between `M`
and pairs `(x, y)` alone does not show that the nested measure is
transported to a product measure. The proof must also derive any needed
sigma-finiteness or product Borel compatibility from the stated hypotheses.
The published integrability lemmas of the two chosen maps supply convergence
of the single Fourier integrands.

## Degenerate rank

The rank `n` is an arbitrary natural number. If `n = 0`, then `M` is the type
of `0 × 1` matrices, which has exactly one point. Then `rowMeasure μ 0` is
the unit point mass (`rowMeasure_zero`), and so is
`rectangularMeasure μ 0 1` (`rectangularMeasure_zero_rows`). The statement
still asserts the displayed equality, and it adds no positive-rank premise.

## Hypotheses not assumed

The proposition adds no product `BorelSpace` instance and no
sigma-finiteness, second countability, continuity of field inversion,
valuation or p-adic structure, and no positive-rank premise. It does not
receive a Fourier map, a change-of-variables formula, a product-measure
compatibility, a Fubini statement or the commutation itself as a hypothesis.
Its only self-duality premise is the existing scalar `IsSelfDual ψ μ`. It
does not replace the Schwartz space, either chosen equivalence, the
character `ψ`, the pairings or the supplied measure.

## Source and provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464. It is registered as `jpss-1983-rankin-selberg` and retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`
with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 1037 recomputed this fingerprint. The scan has no text layer, so
Worker 1037 read the cited pages from rendered page images: Section 6.1,
printed pages 427–428 (one-based PDF pages 62–63), and Section 0.3, printed
pages 375 and 378 (one-based PDF pages 10 and 13).

### Source conventions

On page 375 (Section 0.3) the ground field `F` is local and
non-archimedean. The source restricts it neither to characteristic zero nor
to p-adic fields. On page 378 the source writes `S(a × b, F)` for the
Schwartz–Bruhat functions on the matrices with `a` rows and `b` columns. It
defines the Fourier transform of such a function, depending on the context,
by `∫ Φ(y) ψ(tr(y x)) dy` or `∫ Φ(y) ψ(tr(ᵗy x)) dy`, with a self-invariant
Haar measure `dy`.

### The commutation identity (Section 6.1)

On page 427 the source treats the case `t = r + 1`. It lets `G_t` act on
`S(t − 1 × t, F)` by `(gΦ)(m) = Φ(mg)`, and writes `m = [x, y]` with `y`
the last column of `m`. (The scan says that `x` has as columns "the first
`t − 1` columns of x"; the evident meaning is the first `t − 1` columns of
`m`.) It then defines the partial Fourier transform

`Φ~[x, y] = ∫_{F^(t−1)} Φ[x, u] ψ̄(ᵗy u) du`.

Since `ᵗy u = ∑ i, y i * u i` and `ψ` is unitary, the conjugate character
`ψ̄(ᵗy u)` is `ψ.complex (-rowPairing y u)`. This is
`partialFourierIntegral`, with `n = t − 1`. On page 428, formula (6) defines
the usual Fourier transform

`Φ^(x) = ∫ Φ(y) ψ(tr(y ᵗx)) dy`,

with a plus sign. Since `tr(y ᵗx) = ∑ i, ∑ j, y i j * x i j`, this is
`rectangularFourierIntegral`, with `r = t − 1` and `s = t`. After the
covariance law of the full transform, the source continues: "Using the fact
that `(Φ~)^ = (Φ^)~`, it easily follows that" formula (7). The present
equality is that fact, with `^` read as `F` and `~` read as `T`. The source
states the fact without proof.

### Derived formulation

The present statement is a derived formulation of that identity. JPSS does
not state this exact formulation. The differences are as follows.

- **Chosen maps.** The source applies `~` and `^` as integral operations on
  Schwartz functions. The statement uses the published chosen complex-linear
  equivalences `F` and `T`, which evaluate to the raw integrals and are
  unique given their forward evaluations. This chosen-map API is derived
  packaging of the source operations.
- **Rank.** The source has `t = r + 1`, with `r` the rank of a general
  linear group in Section 6.1. The statement quantifies over every `n : ℕ`
  with `n = t − 1`. Inclusion of the empty rank `n = 0` is derived
  generality.
- **Field.** The source's ground field is a general non-archimedean local
  field. The statement instead assumes the generic typeclass hypotheses
  listed above: a locally compact, Hausdorff, totally disconnected
  topological field with its Borel sets. These hypotheses are a derived
  formal setting. They impose no characteristic restriction, and none is
  attributed to the source.
- **Fourier normalization.** The source fixes a self-invariant Haar measure
  `dy` for its full transform and writes `du` for the partial one. The
  statement packages both through the supplied scalar measure `μ`, the
  explicit scalar hypothesis `IsSelfDual ψ μ`, the nested product
  `rectangularMeasure μ n (n + 1)`, the finite product `rowMeasure μ n` and
  the two chosen equivalences, which require that hypothesis. The statement
  does not assert self-invariance of either product measure; it takes only
  the scalar hypothesis. The shape of the identity does not depend on the
  normalization: in the corresponding pointwise identity written entirely
  with raw integrals, multiplying either product measure by a positive
  constant multiplies both sides by that constant. This remark is explanation only; the Lean statement concerns the
  chosen equivalences alone.

No errata for this source were found. There is no JPSS-specific errata note
in the workspace, the current Library or the shared project notes. The
literature index records no correction for this article.

## Scope

This unit edits no existing Lean/Markdown pair and adds no helper module. It
does not include covariance of the full or partial transform under the right
action, the transported action `rectangularRho0`, or source formula (7). It
also contains no vector-valued integral models, star transforms, Whittaker
spanning, matrix-zeta functional equations, or adjacent-rank gamma or
L-factor analytic statements. Those require separate results against these
actual definitions.
