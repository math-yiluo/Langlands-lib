# Covariance of the full rectangular Schwartz Fourier transform

Worker 1037 authored this statement for task
`b182a14a-23c3-49dc-a05b-b69bf3184836`. Worker 486 published that task as a
focused statement successor under the adjacent-rank gamma/L parent
`b54b4d62-d794-49e6-92ef-2838db2b7f47`. The module states the covariance of
the chosen full rectangular Fourier equivalence under the right action of the
general linear group. It supplies no proof. Its exact-target proof is a
separate later unit.

## The proposition

`Langlands.HarmonicAnalysis.RectangularFourierCovarianceStatement.{uK}` is a
closed proposition definition. Write `M` here only as a prose abbreviation for
the actual type `Matrix (Fin r) (Fin s) K`. The proposition quantifies over an
implicit `K : Type uK` with exactly the instances

```text
[Field K] [TopologicalSpace K] [IsTopologicalRing K]
[MeasurableSpace K] [BorelSpace K]
[LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
```

and then, in this order, over every `ψ : UnitaryAdditiveCharacter K`, every
supplied `μ : AdditiveHaarMeasure K`, all ranks `r s : ℕ`, every proof
`hsd : IsSelfDual ψ μ`, every `g : Langlands.GeneralLinear s K` and every
`Φ : SchwartzBruhat M`. Its body is the equality of actual Schwartz–Bruhat
functions

```text
rectangularFourierEquiv ψ μ r s hsd (rectangularTranslate g Φ) =
  ((((MeasureTheory.distribHaarChar K
      (Langlands.GeneralLinear.determinant g) : ℝ) : ℂ) ^ r)⁻¹) •
    rectangularTranslate (Langlands.GeneralLinear.inverseTranspose s K g)
      (rectangularFourierEquiv ψ μ r s hsd Φ).
```

Write `F = rectangularFourierEquiv ψ μ r s hsd` and
`Δ = MeasureTheory.distribHaarChar K`. The scalar is
`c = ((Δ (det g) : ℂ) ^ r)⁻¹`. Here `Δ (det g)` is a nonnegative real
number, cast first to `ℝ` and then to `ℂ`, raised to the natural power `r`
in `ℂ`, and then inverted in the field `ℂ`. The inverse is the
multiplicative inverse, not a natural exponent with truncated subtraction.
Positivity of `Δ` (Mathlib's `distribHaarChar_pos`) makes the inverted
number nonzero, but the statement does not need this. The scalar acts on
`SchwartzBruhat M` by the existing complex scalar multiplication.

Evaluating at an output matrix `b : M`, the equality entails

```text
F (rectangularTranslate g Φ) b = c * F Φ (b * (g⁻¹).val.transpose).
```

By `rectangularFourierEquiv_apply`, both sides are values of the raw integral
`rectangularFourierIntegral`. The left side is the plus-sign Fourier integral
of `a ↦ Φ (a * g.val)`. The right side is `c` times the Fourier integral of
`Φ` at `b * (g⁻¹).val.transpose`. A private development check confirmed that
the proposition implies this pointwise identity on raw integrals by these
rewrites alone.

## The imported objects

All objects are published ones, imported unchanged by Lean name. The module
introduces no transform, action, pairing, measure, test space or modulus.

- `rectangularFourierEquiv ψ μ r s hsd` from
  [`Langlands.HarmonicAnalysis.RectangularFourierEquiv`](RectangularFourierEquiv.md)
  is the chosen complex-linear equivalence of `SchwartzBruhat M`. Its forward
  value `rectangularFourierEquiv_apply` is
  `rectangularFourierIntegral ψ μ Φ b`, which is
  `∫ a, Φ a * ψ.complex (rectangularPairing a b)` against
  `Langlands.RankinSelberg.rectangularMeasure μ r s`.
- `rectangularPairing a b` is the unsigned entry pairing
  `∑ i, ∑ j, a i j * b i j`, with no conjugation.
- `Langlands.RankinSelberg.rectangularMeasure μ r s` is the nested finite
  product `Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin s => μ.measure))`
  of the supplied scalar measure. It is not a fresh Haar measure or a
  pushforward along a flattening.
- `rectangularTranslate g` from
  [`Langlands.HarmonicAnalysis.RectangularFourier`](RectangularFourier.md) is
  the right action `rectangularTranslate g Φ m = Φ (m * g.val)`, with matrix
  multiplication of the `r × s` matrix `m` by the `s × s` matrix `g.val`.
- `Langlands.GeneralLinear s K` is Mathlib's
  `Matrix.GeneralLinearGroup (Fin s) K`, and
  `Langlands.GeneralLinear.determinant` is Mathlib's unit-valued determinant
  `Matrix.GeneralLinearGroup.det`, both from
  [`Langlands.Group.GL.Basic`](../Group/GL/Basic.md).
- `Langlands.GeneralLinear.inverseTranspose s K` from
  [`Langlands.Group.GL.Maps`](../Group/GL/Maps.md) is the group automorphism
  whose matrix is `(g⁻¹).val.transpose` (lemma `inverseTranspose_coe`).
- `MeasureTheory.distribHaarChar K : Kˣ →* ℝ≥0` is Mathlib's distributive
  Haar character, from `Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean`.
  It is applied to the ordinary scalar action of `Kˣ` on the additive group
  of `K`. For every regular additive Haar measure `ν` on `K`, every unit `a`
  and every set `E`, Mathlib's `distribHaarChar_mul` gives
  `Δ a * ν E = ν (a • E)` in `ℝ≥0∞`, with the evident cast of `Δ a`.
  The supplied `μ.measure` is such a measure, because `AdditiveHaarMeasure`
  carries both the Haar and the regularity instances. The character does not
  depend on the Haar measure.

## Why the exponent is `r` and the action is inverse transpose

This section explains the shape of the law. It is not part of the Lean
statement, and nothing in it is proved here. Put `z = y g` in the integral
`∫ Φ (y g) ψ (⟨y, x⟩) dy`. Right multiplication by `g` acts separately on each
of the `r` rows of `y`. On each row it is a linear automorphism of `Kˢ`,
whose expected modulus for the product of `s` copies of `μ` is `Δ (det g)`.
The pushforward of the nested measure under `y ↦ y g` should therefore be
`(Δ (det g) ^ r)⁻¹` times the nested measure. The pairing transforms as
`⟨z g⁻¹, x⟩ = ⟨z, x (g⁻¹)ᵀ⟩`, since `⟨a, b⟩ = tr (a bᵀ)`. This gives the
scalar `c` and the output action by inverse transpose. The exponent is the
number `r` of rows, not the number `s` of columns. The output action is the
inverse transpose, not the transpose.

A proof must establish these changes of variables for the actual nested
measure `rectangularMeasure μ r s` and the actual Haar character `Δ`. A
coordinate bijection alone does not show that a measure is transported. The
proof must derive any needed sigma-finiteness or product Borel compatibility
from the stated hypotheses. The published `rectangularFourierEquiv_integrable`
supplies convergence of every Fourier integrand.

## Degenerate ranks

Both ranks are arbitrary naturals. If `r = 0`, the scalar is `(Δ (det g) ^ 0)⁻¹ = 1`.
If `s = 0`, then `g = 1`, so the determinant is `1` and the scalar is `1`.
In both cases `M` has exactly one point. The statement still asserts the
displayed equality, and it adds no positive-rank premise.

## Hypotheses not assumed

The proposition adds no product `BorelSpace` instance and no
sigma-finiteness, second countability, continuity of field inversion,
valuation or p-adic structure, and no positive-rank premise. It does not
receive a Fourier map, a determinant scaling identity, a change-of-variables
formula or the covariance law itself as a hypothesis. Its only self-duality
premise is the existing scalar `IsSelfDual ψ μ`. It does not replace the
Schwartz space, the chosen Fourier equivalence, the character `ψ`, the
pairing or the supplied measure.

## Source and provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464. It is registered as `jpss-1983-rankin-selberg` and retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`
with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 1037 recomputed this fingerprint. The scan has no text layer, so
Worker 1037 read the cited pages from rendered page images: Section 0.3,
printed pages 375, 376 and 378 (one-based PDF pages 10, 11 and 13), and
Section 6.1, printed pages 427–428 (one-based PDF pages 62–63).

### Source conventions (Section 0.3)

On page 375 the ground field `F` is local and non-archimedean. The source
restricts it neither to characteristic zero nor to p-adic fields. On page 376,
formula (6) defines `g^ι = ᵗg⁻¹`, the inverse transpose. The same page writes
`|x|` for the absolute value of an element `x` of `F`, after fixing the ring
of integers, its maximal ideal, a generator, the residue cardinality `q` and
the normalized valuation. On page 378, `S(a × b, F)` is the space of
Schwartz–Bruhat functions on the matrices with `a` rows and `b` columns. The
Fourier transform of such a function is defined, depending on the context, by
`∫ Φ(y) ψ(tr(y x)) dy` or `∫ Φ(y) ψ(tr(ᵗy x)) dy`, and the Haar measure `dy`
is self-invariant. So the source normalizes its Fourier measure.

### The covariance law (Section 6.1)

On page 427 the source works with Schwartz functions on the `(t - 1) × t`
matrices, with the action `(gΦ)(m) = Φ(mg)`. Formula (6) on page 428 defines
the usual Fourier transform

`Φ^(x) = ∫ Φ(y) ψ(tr(y ᵗx)) dy`,

with a plus sign. Since `tr(y ᵗx) = ∑ i, ∑ j, y i j * x i j`, this is
`rectangularFourierIntegral`. The unnumbered formula immediately after it
reads

`(gΦ)^ = |det g|^(-(t-1)) g^ι(Φ^)`,

where `g^ι` is the inverse transpose of `g`. This is the present equality
with `r = t - 1` and `s = t`, with `|det g|` read as `Δ (det g)`, and with
`rectangularFourierEquiv` as `Φ ↦ Φ^`.

### Derived formulation

The present statement is a derived generic formulation of that covariance
law. JPSS does not state this exact formulation. The differences are as
follows.

- **Ranks.** The arbitrary ranks `r` and `s`, including the zero ranks and
  the square case `r = s`, are derived generality. The source displays only
  `r = t - 1`, `s = t`.
- **Field.** The source's ground field is a general non-archimedean local
  field. The statement instead assumes the generic typeclass hypotheses listed
  above: a locally compact, Hausdorff, totally disconnected topological field
  with its Borel sets. These hypotheses are a derived formal setting. They
  impose no characteristic restriction, and none is attributed to the source.
- **Modulus.** The source writes `|det g|` with the absolute value `|·|` of
  `F`. The statement uses Mathlib's intrinsic Haar character `Δ` instead. It
  does not identify `Δ` with the normalized absolute value of a local field.
  That comparison is a separate later obligation. Published p-adic and general
  scalar Haar scaling results may serve it.
- **Fourier normalization.** The source fixes a self-invariant Haar measure
  `dy` for its Fourier transform. The statement packages that normalization
  formally through the supplied scalar measure `μ`, the explicit scalar
  self-duality hypothesis `IsSelfDual ψ μ`, the nested product measure
  `rectangularMeasure μ r s` and the chosen equivalence
  `rectangularFourierEquiv`, which requires that hypothesis. The statement
  does not assert that the nested product measure is self-invariant for the
  matrix pairing; it takes only the scalar hypothesis. The shape of the law
  does not depend on the normalization: in the pointwise identity on raw
  integrals, multiplying the matrix measure by a positive constant multiplies
  both sides by that constant. This remark is explanation only; the Lean
  statement concerns the chosen equivalence alone.

No errata for this source were found. There is no JPSS-specific errata note
in the workspace, the current Library or the shared project notes. The
literature index records no correction for this article.

## Scope

This unit edits no existing Lean/Markdown pair and adds no helper module. It
does not include partial Fourier definitions, `rectangularRho0`, covariance
of the partial transform under diagonal, unipotent or scalar elements,
commutation of the full and partial transforms, or source formula (7). It
also contains no vector-valued integral models, star transforms, Whittaker
spanning, matrix-zeta functional equations, or adjacent-rank gamma or
L-factor analytic base. The Section 5.2/5.4 comparisons and the analytic
data remain with Worker 468. Its square specialization `r = s` is available
for their later reuse without transferring that ownership.
