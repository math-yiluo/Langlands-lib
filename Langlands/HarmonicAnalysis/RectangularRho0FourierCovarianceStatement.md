# Full Fourier covariance of the transported action (JPSS formula (7))

Worker 753 authored this statement for task
`870f60ad-4f18-492b-9a9d-9f0d2e4a2290`. Worker 486 published that task as a
statement prerequisite under the adjacent-rank gamma/L parent
`b54b4d62-d794-49e6-92ef-2838db2b7f47`. The module states formula (7) of
JPSS Section 6.1 for the chosen transported action `rectangularRho0` and the
chosen full rectangular Fourier equivalence. It supplies no proof. Its
exact-target proof is a separate later unit.

## The proposition

`Langlands.HarmonicAnalysis.RectangularRho0FourierCovarianceStatement.{uK}`
is a closed proposition definition. Write `M` here only as a prose
abbreviation for the actual type `Matrix (Fin n) (Fin (n + 1)) K`. The
proposition quantifies over an implicit `K : Type uK` with exactly the
instances

```text
[Field K] [TopologicalSpace K] [IsTopologicalRing K]
[MeasurableSpace K] [BorelSpace K]
[LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
```

and then, in this order, over every `ψ : UnitaryAdditiveCharacter K`, every
supplied `μ : AdditiveHaarMeasure K`, every rank `n : ℕ`, every proof
`hsd : IsSelfDual ψ μ`, every `g : Langlands.GeneralLinear (n + 1) K` and
every `Φ : SchwartzBruhat M`. Its body is the equality of actual
Schwartz–Bruhat functions

```text
rectangularFourierEquiv ψ μ n (n + 1) hsd (rectangularRho0 ψ μ n hsd g Φ) =
  ((((MeasureTheory.distribHaarChar K
      (Langlands.GeneralLinear.determinant g) : ℝ) : ℂ) ^ n)⁻¹) •
    rectangularRho0 ψ μ n hsd (Langlands.GeneralLinear.inverseTranspose (n + 1) K g)
      (rectangularFourierEquiv ψ μ n (n + 1) hsd Φ).
```

Write `F = rectangularFourierEquiv ψ μ n (n + 1) hsd`,
`T = partialFourierEquiv ψ μ n hsd`, `ρ = rectangularRho0 ψ μ n hsd`,
`Δ = MeasureTheory.distribHaarChar K` and `gι` for
`Langlands.GeneralLinear.inverseTranspose (n + 1) K g`. The statement reads
`F (ρ g Φ) = c • ρ gι (F Φ)` with the scalar
`c = ((Δ (det g) : ℂ) ^ n)⁻¹`. Here `Δ (det g)` is a nonnegative real
number, cast first to `ℝ` and then to `ℂ`, raised to the natural power `n`
in `ℂ`, and then inverted in the field `ℂ`. The inverse is the
multiplicative inverse, not a natural exponent with truncated subtraction.
The exponent is the number `n` of rows. The scalar acts on `SchwartzBruhat M`
by the existing complex scalar multiplication. The group element on the
right is the inverse transpose of `g`, not `g` and not its transpose.

By `rectangularRho0_apply`, `ρ g Φ` is the Schwartz function
`T (rectangularTranslate g (T.symm Φ))`. Evaluating at an output matrix
`b : M` and using `rectangularFourierEquiv_apply` and
`partialFourierEquiv_apply`, the equality entails the identity of raw
integrals

```text
rectangularFourierIntegral ψ μ (T (rectangularTranslate g (T.symm Φ))) b =
  c * partialFourierIntegral ψ μ (rectangularTranslate gι (T.symm (F Φ))) b.
```

A private development check confirmed that the proposition implies this
pointwise identity by these rewrites and the pointwise form of the scalar
action alone. The same check printed the elaborated proposition: the left
side applies `F` to `ρ g Φ`, and the right side is `c • ρ gι (F Φ)` with
`c` as described.

## The imported objects

All objects are published ones, imported unchanged by Lean name. The module
introduces no transform, action, pairing, measure, test space or modulus.

- `rectangularFourierEquiv ψ μ n (n + 1) hsd` from
  [`Langlands.HarmonicAnalysis.RectangularFourierEquiv`](RectangularFourierEquiv.md)
  is the chosen complex-linear equivalence of `SchwartzBruhat M`, at row
  rank `n` and column rank `n + 1`. Its forward value
  `rectangularFourierEquiv_apply` is `rectangularFourierIntegral ψ μ Φ b`,
  which is `∫ a, Φ a * ψ.complex (rectangularPairing a b)` against
  `Langlands.RankinSelberg.rectangularMeasure μ n (n + 1)`. This is the
  plus-sign transform.
- `rectangularPairing a b` from
  [`Langlands.HarmonicAnalysis.RectangularFourier`](RectangularFourier.md)
  is the unsigned entry pairing `∑ i, ∑ j, a i j * b i j`, with no
  conjugation.
- `Langlands.RankinSelberg.rectangularMeasure μ n (n + 1)` is the nested
  finite product of `n` copies of the product of `n + 1` copies of the
  supplied scalar measure `μ.measure`. It is not a fresh Haar measure.
- `partialFourierEquiv ψ μ n hsd` and `rectangularRho0 ψ μ n hsd` come from
  [`Langlands.HarmonicAnalysis.PartialFourierEquiv`](PartialFourierEquiv.md).
  The first is the chosen equivalence `T` whose forward value
  `partialFourierIntegral ψ μ Φ m` transforms only the last column of `m`,
  with the inverse character `ψ.complex (-rowPairing y u)` against
  `rowMeasure μ n`. The second is the representation
  `Representation ℂ (Langlands.GeneralLinear (n + 1) K) (SchwartzBruhat M)`
  whose value at `g` is the conjugate `T ∘ R_g ∘ T.symm` of the right
  action. So `ρ` keeps the original inverse-character last-column
  transform.
- `rectangularTranslate g` from
  [`Langlands.HarmonicAnalysis.RectangularFourier`](RectangularFourier.md)
  is the right action `R_g`, with
  `rectangularTranslate g Φ m = Φ (m * g.val)`.
- `Langlands.GeneralLinear (n + 1) K` is Mathlib's
  `Matrix.GeneralLinearGroup (Fin (n + 1)) K`, and
  `Langlands.GeneralLinear.determinant` is Mathlib's unit-valued determinant
  `Matrix.GeneralLinearGroup.det`, both from
  [`Langlands.Group.GL.Basic`](../Group/GL/Basic.md).
- `Langlands.GeneralLinear.inverseTranspose (n + 1) K` from
  [`Langlands.Group.GL.Maps`](../Group/GL/Maps.md) is the group automorphism
  whose matrix is `(g⁻¹).val.transpose` (lemma `inverseTranspose_coe`).
- `MeasureTheory.distribHaarChar K : Kˣ →* ℝ≥0` is Mathlib's distributive
  Haar character, from `Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean`.
  It is applied to the ordinary scalar action of `Kˣ` on the additive group
  of `K`. By Mathlib's `distribHaarChar_mul`, it gives the factor by which
  a unit scales every regular additive Haar measure on `K`. It does not
  depend on the Haar measure.

## How formula (7) follows in the source

This section explains the shape of the law. It is not part of the Lean
statement, and nothing in it is proved or assumed here. The source derives
formula (7) from two identities. The first is full Fourier covariance,
`F (R_g Ψ) = c • R_gι (F Ψ)` for every Schwartz function `Ψ`. The second is
the commutation `F (T Ψ) = T (F Ψ)` of the full and partial transforms,
which also gives `F (T.symm Ψ) = T.symm (F Ψ)`. Then

```text
F (ρ g Φ) = F (T (R_g (T.symm Φ)))
          = T (F (R_g (T.symm Φ)))
          = T (c • R_gι (F (T.symm Φ)))
          = c • T (R_gι (T.symm (F Φ)))
          = c • ρ gι (F Φ).
```

The covariance step is the published statement
`Langlands.HarmonicAnalysis.RectangularFourierCovarianceStatement` at
`r = n` and `s = n + 1`, with the same scalar. The commutation of the chosen
full and partial transforms is a separate later statement. Neither is a
hypothesis of the present proposition, and this module does not import the
covariance statement. A proof of the present proposition must establish
their mathematical content for the actual chosen maps.

## Rank zero

The rank `n` is an arbitrary natural, including `n = 0`. Then `M` is the
type of `0 × 1` matrices, which has exactly one point, `g` is an invertible
`1 × 1` matrix, and the scalar is `(Δ (det g) ^ 0)⁻¹ = 1`. The statement
still asserts the displayed equality, and it adds no positive-rank premise.
Section 6.1 of the source treats `t = r + 1`, where `r` is the rank of the
group `G_r` of a representation `π`, so its `t - 1` is positive. The case
`n = 0` is a derived extension.

## Hypotheses not assumed

The proposition adds no product `BorelSpace` instance and no
sigma-finiteness, second countability, continuity of field inversion,
valuation or p-adic structure, and no positive-rank premise. It does not
receive a Fourier map, a determinant scaling identity, a change-of-variables
formula, full Fourier covariance, full/partial commutation or formula (7)
itself as a hypothesis. Its only self-duality premise is the existing scalar
`IsSelfDual ψ μ`. It does not replace the Schwartz space, the chosen full
or partial Fourier equivalence, the transported action, the character `ψ`,
the pairing or the supplied measure.

## Source and provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464. It is registered as `jpss-1983-rankin-selberg` and retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`
with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 753 recomputed this fingerprint. The scan has no text layer, so
Worker 753 read the cited pages from page images rendered from that file:
Section 0.3, printed pages 376 and 378 (one-based PDF pages 11 and 13),
and Section 6.1, printed pages 427–428 (one-based PDF pages 62–63).

### Source conventions

On page 376, formula (6) of Section 0.3 defines `g^ι = ᵗg⁻¹`, the inverse
transpose, and the same page writes `|x|` for the absolute value of an
element `x` of the local field `F`. On page 378, `S(a × b, F)` is the
space of Schwartz–Bruhat functions on the matrices with `a` rows and `b`
columns, and the Haar measure `dy` of a Fourier transform is
self-invariant. On page 427, Section 6.1 lets `G_t` act
on the `(t - 1) × t` matrices by `m ↦ m g⁻¹`, with dual action
`(gΦ)(m) = Φ(mg)` on Schwartz functions. It writes `m = [x, y]`, with `y`
the last column, and defines the partial transform
`Φ~[x, y] = ∫ Φ[x, u] ψ̄(ᵗy u) du` over `F^(t-1)`. On page 428, formula (2)
defines `ρ₀` by `ρ₀(g)(Φ~) = (gΦ)~`. Formula (6) defines the usual Fourier
transform `Φ^(x) = ∫ Φ(y) ψ(tr(y ᵗx)) dy`, with a plus sign. Since
`tr(y ᵗx) = ∑ i, ∑ j, y i j * x i j`, this is `rectangularFourierIntegral`.

### Formula (7)

The page continues: "Then `(gΦ)^ = |det g|^(-(t-1)) g^ι(Φ^)`. Using the
fact that `(Φ~)^ = (Φ^)~`, it easily follows that

(7) `(ρ₀(g)Φ)^ = |det g|^(-(t-1)) ρ₀(g^ι)(Φ^)`."

The present proposition is formula (7) with `n = t - 1`, with `Φ ↦ Φ^` read
as `rectangularFourierEquiv`, `ρ₀` as `rectangularRho0`, `g^ι` as
`Langlands.GeneralLinear.inverseTranspose (n + 1) K g`, and `|det g|` read
as `Δ (det g)`. The source's negative power `|det g|^(-(t-1))` is the
multiplicative inverse of the `n`-th power.

### Derived formulation

The present statement is a derived generic formulation of formula (7). JPSS
does not state this exact formulation. The differences are as follows.

- **Chosen API.** The source's `Φ~` and `ρ₀` are realized by the published
  chosen equivalence `partialFourierEquiv` and the representation
  `rectangularRho0 = T ∘ R_g ∘ T.symm`, whose intertwining lemma
  `rectangularRho0_intertwine` is the source's formula (2). The source's
  `Φ^` is realized by the published chosen equivalence
  `rectangularFourierEquiv`. These are derived internal packaging of
  published existence theorems; the statement concerns these actual maps.
- **Field.** The source's ground field is a non-archimedean local field.
  The statement instead assumes the generic typeclass hypotheses listed
  above: a locally compact, Hausdorff, totally disconnected topological field
  with its Borel sets. These hypotheses are a derived formal setting. They
  impose no characteristic restriction, and none is attributed to the
  source.
- **Modulus.** The source writes `|det g|` with the absolute value of `F`.
  The statement uses Mathlib's intrinsic Haar character `Δ` instead. It does
  not identify `Δ` with the normalized absolute value of a local field. That
  comparison is a separate later obligation.
- **Fourier normalization.** The source takes self-invariant Haar
  measures for its Fourier transforms. The statement packages that normalization through the supplied scalar measure
  `μ`, the explicit scalar self-duality hypothesis `IsSelfDual ψ μ`, the
  nested product measures `rectangularMeasure μ n (n + 1)` and
  `rowMeasure μ n`, and the chosen equivalences, which require that
  hypothesis. It does not assert that the nested product measure is
  self-dual for the matrix pairing; it takes only the scalar hypothesis.
- **Rank and values.** The source's `t - 1` is positive; the statement
  includes `n = 0`. The source also uses the same notation for vector-valued
  functions; the statement concerns only complex-valued Schwartz–Bruhat
  functions.

No errata for this source were found. There is no JPSS-specific errata note
in the workspace, the current Library notes or the shared project notes, and
the literature index records no correction for this article.

## Scope

This unit edits no existing Lean/Markdown pair and adds no helper module. It
contains no proof of formula (7), of full Fourier covariance or of the
commutation of the full and partial transforms. It does not identify the
Haar character with the normalized p-adic absolute value. It also contains
no vector-valued models, star transforms, Whittaker spanning, or gamma or
L-factor analytics, and it closes neither analytic parent target.
