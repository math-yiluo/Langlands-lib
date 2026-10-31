# Elementary covariance of the chosen partial Fourier action

Worker 252 wrote this statement unit for the adjacent-rank Rankin–Selberg
work coordinated by Worker 486 (parent task `b54b4d62`). It states how the
transported JPSS action `rectangularRho0` from
[`PartialFourierEquiv`](PartialFourierEquiv.md) acts on three kinds of
elementary matrices. These are JPSS Section 6.1 formulas (3), (4) and (5).
The file supplies no proof. The proof that targets this exact proposition is
a later, separate unit.

## The proposition

`Langlands.HarmonicAnalysis.PartialFourierCovarianceStatement.{uK}` is a
closed proposition definition. Its universe `uK` is arbitrary. It
quantifies over an implicit `K : Type uK` with exactly the instances

```text
[Field K] [TopologicalSpace K] [IsTopologicalRing K]
[MeasurableSpace K] [BorelSpace K]
[LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
```

and then over `ψ : UnitaryAdditiveCharacter K`, a supplied
`μ : AdditiveHaarMeasure K`, `n : ℕ` and `hsd : IsSelfDual ψ μ`. The
self-duality `hsd` is the only premise. The conclusion is the conjunction
of the three laws below, in this order. Each law is universally quantified
over its displayed inputs.

In this note `S` stands for the actual type
`SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)` and `ρ` stands for
`rectangularRho0 ψ μ n hsd`. These are prose abbreviations only; the Lean
source writes both out in full and supplies no extra map or hypothesis.
Recall from the published input that

```text
ρ g Φ = T (rectangularTranslate g (T.symm Φ)),
rectangularTranslate g Φ m = Φ (m * g.val),
```

where `T = partialFourierEquiv ψ μ n hsd` is the chosen last-column
partial Fourier equivalence. For `m = [x,y]` it evaluates to
`∫ Φ[x,u] ψ(-∑ i, y i * u i) du` over the product measure
`rowMeasure μ n`. Its inverse uses the plus character.

**Law 1 (formula (3)).** For every `h : GeneralLinear n K` and `Φ : S`,

```text
ρ (rankInclusion 1 h) Φ = rectangularTranslate (rankInclusion 1 h) Φ
```

as an equality in `S`. Here `GeneralLinear.rankInclusion 1 h` is
`blockSum (h, 1)`, the actual block-diagonal matrix `diag(h, 1)` in
`GeneralLinear (n + 1) K`.

**Law 2 (formula (4)).** For every `v : Fin n → K`, `Φ : S`,
`x : Matrix (Fin n) (Fin n) K` and `y : Fin n → K`, set

```text
u = GeneralLinear.blockUnipotent (a := n) (b := 1) (n := n + 1) rfl
      (fun i _ => v i).
```

This is the actual upper unipotent matrix `[[I_n, v], [0, 1]]`, whose last
column above the diagonal is `v`. The law is the pointwise equality

```text
ρ u Φ (rectangularJoin x y) =
  Φ (rectangularJoin x y) * ψ.complex (rowPairing y (Matrix.mulVec x v)).
```

The character sign is plus. The pairing is `∑ i, y i * (x v) i`, with the
matrix-vector product `x v`, not `xᵀ v`. Every `n × (n + 1)` matrix is
`rectangularJoin x y` for its first `n` columns `x` and its last column
`y`. Law 2 therefore determines `ρ u Φ` at every point. It is stated
pointwise because its right-hand side is a plain function, not an element
of `S`.

**Law 3 (formula (5)).** For every `a : Kˣ` and `Φ : S`, set

```text
d = GeneralLinear.blockSum
      ((1 : GeneralLinear n K), GeneralLinear.scalar (n := 1) a)
c = (((MeasureTheory.distribHaarChar K a : ℝ) : ℂ) ^ n)⁻¹.
```

Thus `d = diag(1, …, 1, a)`. The law is the equality in `S`

```text
ρ d Φ = c • rectangularTranslate d⁻¹ Φ,
```

with complex scalar multiplication. The factor `c` is the multiplicative
inverse of the `n`-th natural power of the real Haar character, cast to `ℂ`.

The elementary matrices are the published ones, used by Lean name:
`rankInclusion` and `blockSum` from
[`Group/GL/RankMaps`](../Group/GL/RankMaps.md), `blockUnipotent` from
[`Group/GL/BlockUnipotent`](../Group/GL/BlockUnipotent.md) and `scalar`
from [`Group/GL/Basic`](../Group/GL/Basic.md). All of them place the first
`n` coordinates before the final coordinate, as `rectangularJoin` does.
The objects `rectangularTranslate` and `rectangularJoin` come from
[`RectangularFourier`](RectangularFourier.md), and `rowPairing` comes from
[`RowFourier`](RowFourier.md). `partialFourierEquiv` and
`rectangularRho0` come from [`PartialFourierEquiv`](PartialFourierEquiv.md).
None of these pairs is changed.

### The Haar character

`MeasureTheory.distribHaarChar K : Kˣ →* ℝ≥0` is Mathlib's positive
character of the multiplication action of `Kˣ` on the additive group `K`.
For every regular additive Haar measure it satisfies
`distribHaarChar K a * μ E = μ (a • E)` (`distribHaarChar_mul`). This
holds in particular for the supplied `μ`, because `AdditiveHaarMeasure`
records both the Haar property and regularity. Write `Δ(a)` for this
character. Then `c = Δ(a)^(-n)`.

Here is why the sign and exponent are as stated. With
`F = T.symm Φ`, right translation by `d` sends the last column `u` to
`a u`. Hence `ρ d Φ [x,y]` is the iterated integral of
`Φ[x,w] ψ(∑ i, (a u) i * w i) ψ(-∑ i, y i * u i)`. Changing variables in
`w` on the `n`-fold product measure gives a factor `Δ(a)^(-n)`. Fourier
inversion then leaves `Φ[x, a⁻¹ y]`, which is
`rectangularTranslate d⁻¹ Φ [x,y]`. This sketch is a guide for the later
proof, which must justify the change of variables on the actual
`rowMeasure μ n`. It is not part of the proposition.

### Scope of the premises

The case `n = 0` is included. The matrix space then has a single point, so
every right translation acts trivially. The pairing in Law 2 is the empty
sum `0`, and the factor in Law 3 is `1`. Each law then reduces to an
identity.

The proposition adds none of the following premises: a Borel structure on
the product spaces, sigma-finiteness, second countability, continuity of
inversion, a p-adic field, a valuation, positive rank, any covariance
hypothesis, determinant scaling, or a change-of-variables formula. It uses
the actual whole-matrix Schwartz–Bruhat space and the supplied measure. It
replaces neither with an all-functions space nor with the range of a chosen
map.

## Source and provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, Section 6.1, printed pages 427–428 (one-based PDF pages 62–63).
The registered source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The hash was verified, and printed pages 427 and 428 were read visually
from the scan. No erratum is registered for this source: its central-library
pointer lists none, and the Library has no source-specific JPSS errata
note.

Page 427 defines `Φ~[x,y] = ∫ Φ[x,u] ψ̄(ᵗy u) du` on `S(t − 1 × t, F)`.
Formula (2) on page 428 sets `ρ0(g)(Φ~) = (gΦ)~`, where `(gΦ)(m) = Φ(mg)`.
The source then says that "one easily deduces" the following formulas:

- (3) if `g = diag(h, 1)` with `h ∈ G_{t−1}`, then `ρ0(g)Φ = gΦ`;
- (4) if `u = [[1_{t−1}, v], [0, 1]]` and `m = [x,y]`, then
  `ρ0(u)Φ(m) = Φ(m) ψ(ᵗy x v)`;
- (5) if `g = diag(1, 1, …, a)`, then `ρ0(g)Φ = |a|^{−(t−1)} g⁻¹Φ`.

The correspondence is as follows. The source's `t − 1` is `n` here. Its
right action `gΦ` is `rectangularTranslate g Φ`. Its partial transform
`Φ ↦ Φ~`, with inverse character in the last column, is the chosen
`partialFourierEquiv`, and `ρ0` is `rectangularRho0`. The published input
already proves formula (2) as `rectangularRho0_intertwine`. Laws 1 and 2
are formulas (3) and (4) as printed: `ᵗy x v` is
`rowPairing y (Matrix.mulVec x v)`. The source's `g⁻¹Φ` in formula (5) is
`rectangularTranslate d⁻¹ Φ`.

The following parts are derived, not transcribed from the printed source:

- **The scalar factor.** The source writes `|a|^{−(t−1)}` for the
  normalized absolute value of its non-archimedean local field. Law 3
  writes `Δ(a)^(-n)` with Mathlib's generic Haar character instead, the
  scalar describing `μ(aE) = Δ(a) μ(E)`. This is the form in which the
  formula follows from a change of variables for the supplied product
  measure, and that justification is left to the later proof. Identifying
  `Δ` with the normalized p-adic absolute value is a separate question and
  is not asserted here.
- **The generic field.** `K` is an arbitrary field with the displayed
  instances, rather than a non-archimedean local field. The only analytic
  premise is `IsSelfDual ψ μ`, under which the chosen equivalence exists.
- **Zero rank.** The source does not treat the degenerate case `t = 1`
  separately. Here `n = 0` is included explicitly, and every law reduces
  to an identity.
- **Packaging.** The three formulas are combined into one conjunction.
  Law 2 is stated pointwise at `[x,y]`, as in the source.

This statement does not include formula (2), which is already proved in
the input. It also does not include the commutation of the full and
partial Fourier transforms, full Fourier covariance (formula (6) and the
display after it), formula (7), vector-valued or Whittaker integral
models, or gamma and L-function analytics. Those are separate units.
