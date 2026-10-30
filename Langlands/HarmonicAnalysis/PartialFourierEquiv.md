# Chosen partial Fourier equivalence and JPSS transported action

Worker 455 packages the already published last-column Fourier theorem and
right Schwartz action into named definitions. The module imports
[`PartialFourierCompatibilityProof`](PartialFourierCompatibilityProof.md)
by Lean name and leaves that proof, its statement, and the underlying
[`RectangularFourier`](RectangularFourier.md) objects unchanged. The new
content is derived internal API and elementary algebraic proofs.

## Parameters and actual test space

All definitions and lemmas are in `Langlands.HarmonicAnalysis`. They retain
an implicit arbitrary `K : Type uK` with exactly

```text
[Field K] [TopologicalSpace K] [IsTopologicalRing K]
[MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
[T2Space K] [TotallyDisconnectedSpace K]
```

Their explicit parameters are `ψ : UnitaryAdditiveCharacter K`,
`μ : AdditiveHaarMeasure K`, `n : ℕ`, and `hself : IsSelfDual ψ μ`, in
that order. Write `M = Matrix (Fin n) (Fin (n + 1)) K` and
`S = SchwartzBruhat M` in this explanation. These abbreviations are prose:
the Lean declarations use the actual whole-matrix Schwartz space, whose
functions are locally constant and compactly supported on all matrix
variables together.

There is no product Borel-space, sigma-finiteness, second-countability,
field-inversion continuity, valuation, p-adic-field, nontrivial-character,
or positive-rank premise. The supplied measure is retained throughout.
Every construction includes `n = 0`; no argument uses a nonempty row index.

## Choice, evaluation, convergence and uniqueness

`partialFourierEquiv ψ μ n hself : S ≃ₗ[ℂ] S` is defined by

```text
Classical.choose (partialFourierCompatibility ψ μ n hself).
```

This is a noncomputable choice of an actual complex-linear equivalence
from a proved existential. The corresponding `Classical.choose_spec`
contains the existing four clauses, in their original conjunction order.
The following public lemmas project them:

| Lemma | Conclusion for every `Φ : S` and `m : M` |
| --- | --- |
| `partialFourierEquiv_apply` | `T Φ m = partialFourierIntegral ψ μ Φ m` |
| `partialFourierEquiv_symm_apply` | `T.symm Φ m = partialFourierPlusIntegral ψ μ Φ m` |
| `partialFourierEquiv_integrable` | The inverse-character integrand below is integrable |
| `partialFourierEquiv_plus_integrable` | The plus-character integrand below is integrable |

Here `T = partialFourierEquiv ψ μ n hself`. For `m = [x,y]` the
integrands are exactly

```text
u ↦ Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex (-rowPairing (rectangularLastColumn m) u),
u ↦ Φ (rectangularJoin (rectangularFirstColumns m) u) *
      ψ.complex ( rowPairing (rectangularLastColumn m) u).
```

Both convergence statements use the original `rowMeasure μ n`, with its
finite product measurable structure. They assert convergence of the
actual integrands for every Schwartz input, so they apply also to outputs
of `T` and `T.symm`. The forward map transforms only the last column,
with the inverse character; its inverse uses the plus character.

`partialFourierEquiv_symm_apply_apply` and
`partialFourierEquiv_apply_symm_apply` expose the two inverse identities
as equalities of Schwartz functions. They are the existing inverse laws
of the chosen `LinearEquiv`.

`partialFourierEquiv_unique` takes any other `E : S ≃ₗ[ℂ] S` and the
pointwise forward evaluation
`∀ Φ m, E Φ m = partialFourierIntegral ψ μ Φ m`, and proves `E = T`.
The proof applies `LinearEquiv.ext`, then extensionality of the actual
Schwartz functions. At each matrix both values equal the same integral.
Thus uniqueness is equality of maps; it does not assert that witnesses
obtained by choice are definitionally equal.

## The transported representation

`rectangularRho0 ψ μ n hself` has type

```text
Representation ℂ (Langlands.GeneralLinear (n + 1) K) S.
```

Its defining linear endomorphism at `g` is
`T.toLinearMap.comp (R_g.comp T.symm.toLinearMap)`, where `R_g` is
the published `rectangularSchwartzRepresentation g`. The evaluation lemma
`rectangularRho0_apply` is the resulting equality in `S`:

```text
rectangularRho0 ψ μ n hself g Φ =
  T (rectangularTranslate g (T.symm Φ)).
```

The published action uses `(rectangularTranslate g Φ)(m) = Φ(m * g.val)`.
The representation's identity law follows from
`rectangularTranslate_one` and `T (T.symm Φ) = Φ`. Its multiplication
law uses `rectangularTranslate_mul` and cancels
`T.symm (T Ψ) = Ψ` between the two actions. Both laws are proved in
the construction; no new action or group law is assumed. The public
lemmas `rectangularRho0_one` and `rectangularRho0_mul` also expose them
on Schwartz inputs.

Finally `rectangularRho0_intertwine` substitutes `T Φ` in the evaluation
formula and cancels `T.symm (T Φ)`. It gives exactly

```text
rectangularRho0 ψ μ n hself g (T Φ) =
  T (rectangularTranslate g Φ).
```

The whole representation therefore acts on the same actual Schwartz
space, rather than on all functions, a quotient, or a chosen range.

## Original source and derived provenance

The convention comes from H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, Section 6.1, printed pp.427–428 (one-based PDF
pp.62–63). The registered original is `jpss-1983-rankin-selberg` at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 455 verified the hash and visually read both scanned pages.
The registered pointer lists no erratum, and no source-specific
`notes/errata/jpss-1983-rankin-selberg.md` was found in the workspace,
project notes or current Library notes.

At the bottom of p.427 the source splits a matrix in `M(t − 1 × t)`
as `[x,y]`, with `y` its last column, and defines the partial transform
using the conjugate character of the pairing of `y` with the integration
variable. Our `n` is `t − 1`. Unitarity identifies that conjugate with
`ψ.complex (-rowPairing y u)`, precisely the forward map above. The
natural dual action is right translation `Φ(mg)`. Formula (2) on p.428
defines its twist by `ρ₀(g)(Φ~) = (gΦ)~`. The proved intertwining
identity implements that equation with the orientation `T R_g T.symm`.

The choice of a named equivalence, the four projection lemmas,
extensional uniqueness, and the bundled representation and elementary
group laws are derived internal packaging of the published
`partialFourierCompatibility` and right action. They are not claimed as
separate verbatim theorems of JPSS. The generic field telescope,
arbitrary universe and inclusion of `n = 0` are inherited from the
published theorem.

This unit supplies no diagonal, unipotent or scalar covariance formulas,
commutation with the full Fourier transform, formula (7), vector-valued
Whittaker integrals, spanning or star transforms, analytic gamma/L base
theorems, or square-matrix analytic comparisons. Those require separate
results against these actual definitions.
