# Last-column partial Fourier equivalence and convergence

Worker 252 authored this statement unit for the adjacent-rank Rankin–Selberg
work coordinated by Worker 486 (task `b54b4d62`). It states that the raw
last-column partial Fourier integrals of
[`Langlands.HarmonicAnalysis.RectangularFourier`](RectangularFourier.md)
form an actual linear equivalence of rectangular Schwartz–Bruhat spaces. The
file supplies no proof.

## The proposition

`Langlands.HarmonicAnalysis.PartialFourierCompatibilityStatement.{uK}` is a
closed proposition definition. Its universe `uK` is arbitrary. It quantifies
over an implicit `K : Type uK` with exactly the instances

```text
[Field K] [TopologicalSpace K] [IsTopologicalRing K]
[MeasurableSpace K] [BorelSpace K]
[LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
```

Then come `ψ : UnitaryAdditiveCharacter K`, a supplied
`μ : AdditiveHaarMeasure K`, and `n : ℕ`. The only premise is
`IsSelfDual ψ μ`. In this note `M` is a prose abbreviation for the actual
type `Matrix (Fin n) (Fin (n + 1)) K`; the Lean source writes the matrix type
out in full. The conclusion is an existential followed by a conjunction of four
clauses:

```text
∃ T : SchwartzBruhat M ≃ₗ[ℂ] SchwartzBruhat M,
  (∀ Φ m, T Φ m = partialFourierIntegral ψ μ Φ m) ∧
  (∀ Φ m, T.symm Φ m = partialFourierPlusIntegral ψ μ Φ m) ∧
  (∀ Φ m, MeasureTheory.Integrable
     (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (-rowPairing (rectangularLastColumn m) u))
     (rowMeasure μ n)) ∧
  (∀ Φ m, MeasureTheory.Integrable
     (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (rowPairing (rectangularLastColumn m) u))
     (rowMeasure μ n))
```

Here `Φ` ranges over `SchwartzBruhat M` and `m` over `M`. Clause 1 says that
the forward map evaluates to the inverse-character integral. With `m = [x,y]`,
that integral is `∫ Φ[x,u] ψ(-∑ i, y i * u i) du` over the row space
`Fin n → K`. Clause 2 says the inverse map evaluates to the plus-character
companion. Clause 3 gives integrability of the inverse-character integrand on
every slice, and clause 4 does the same for the plus-character integrand.

The meaning of each clause:

- `T` is an actual complex-linear equivalence. It therefore carries both
  inverse laws, `T.symm (T Φ) = Φ` and `T (T.symm Φ) = Φ`, not merely
  injectivity or surjectivity of an unspecified function.
- The codomain of `T` and of `T.symm` is the actual Schwartz–Bruhat space:
  locally constant, compactly supported complex functions on the whole matrix
  space. This is uniform in all variables, not only on each fixed slice.
- The integrals in clauses 1 and 2 are Bochner integrals, which return zero on
  non-integrable integrands. Clauses 3 and 4 assert that these are genuine
  convergent integrals. The convergence clauses quantify over every
  `SchwartzBruhat M` input, so they also apply to `T Φ` and `T.symm Φ`. This
  covers the iterated integrals used by inversion.
- The measure is the existing `rowMeasure μ n`, the finite product of the
  supplied scalar measure, with its product measurable structure on
  `Fin n → K`. No new measure or normalization is introduced.

The case `n = 0` is included. There the row space `Fin 0 → K` has one point,
and `rowMeasure μ 0` is the Dirac mass at that point (`rowMeasure_zero`).
Both partial integrals then reduce to evaluating `Φ` at `m`.

The target adds none of the following premises: scalar or product
sigma-finiteness, a Borel-space instance on the row or matrix space, second
countability, continuity of field inversion, a valuation, a p-adic structure,
row or partial Fourier closure or inversion, a supplied Fourier equivalence,
or an additional normalization of `μ`. A proof must derive any such ingredient
from the displayed hypotheses and published results. For example, the
published `scalarFourierClosure` derives scalar sigma-finiteness from
`IsSelfDual`. For this reason the statement uses the raw integrals
`partialFourierIntegral` and `partialFourierPlusIntegral` rather than the
bundled `partialFourierTransform` maps. Those maps carry explicit
`SigmaFinite μ.measure` and `BorelSpace (Fin n → K)` assumptions.

All objects are imported unchanged by Lean name.
[`Basic`](Basic.md) supplies `SchwartzBruhat`, `UnitaryAdditiveCharacter`,
`AdditiveHaarMeasure` and `IsSelfDual`. [`RowFourier`](RowFourier.md)
supplies `rowMeasure` and `rowPairing`.
[`RectangularFourier`](RectangularFourier.md) supplies `rectangularJoin`,
`rectangularFirstColumns`, `rectangularLastColumn`, `partialFourierIntegral`
and `partialFourierPlusIntegral`.

## Source and provenance

The source construction is in H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, Section 6.1, printed pages 427–428 (one-based PDF pages
62–63). The registered source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both scanned pages were visually checked. No erratum for this source is
registered. Its central-library pointer lists none, the Library has no
`notes/errata/jpss-1983-rankin-selberg.md`, and the Whittaker/Rankin–Selberg
external audit note records none in the checked errata locations.

At the bottom of page 427 the source takes `m ∈ M(t − 1 × t)` and writes
`m = [x,y]`. Here `x` is the `(t − 1) × (t − 1)` block of the first `t − 1`
columns and `y` is the last column. For `Φ` in `S(t − 1 × t, F)` it sets

```text
Φ~[x,y] = ∫_{F^{t-1}} Φ[x,u] ψ̄(ᵗy u) du.
```

The source then twists the natural action `(gΦ)(m) = Φ(mg)` by this partial
transform to define the action `ρ0`, by formula (2) on page 428:
`ρ0(g)(Φ~) = (gΦ)~`. Our `n` is the source's `t − 1`. Since `ψ` is unitary,
`ψ̄(ᵗy u) = ψ(-∑ i, y i * u i)`, which is the inverse character used by
`partialFourierIntegral`. That integral is therefore the forward map `T`, and
the plus-character companion is `T.symm`. Pages 427–428 write `du` without
restating a normalization. Here the product measure is built from the supplied
`μ`, and self-duality is the premise that makes the plus-character integral
the inverse. Indeed, scalar self-duality gives row inversion in the form
"plus transform twice equals reflection". The inverse-character transform is
the plus transform composed with `y ↦ -y`, so the two transforms are mutually
inverse.

Formula (2) defines `ρ0` on all of `S(t − 1 × t, F)`. That definition
presupposes that `Φ ↦ Φ~` is a bijection of the Schwartz space with
convergent integrals. The source does not state this as a separate result.
This proposition makes it explicit. The following are derived internal
interfaces that support the source construction, not transcriptions of a
printed theorem:

- the explicit linear equivalence with its named inverse;
- the packaging of convergence as separate clauses;
- the arbitrary generic topological field `K` in place of the source's
  non-archimedean local field, under the displayed instances;
- the zero-dimensional case `n = 0`.

This statement supplies no analytic base proof. It also supplies no
Fourier-conjugated action `ρ0`, no covariance formula among (2)–(5) and (7)
on page 428, no vector-valued Whittaker integral, and no full rectangular
Fourier theorem. Those are separate units, to be stated against the proved
equivalence.
