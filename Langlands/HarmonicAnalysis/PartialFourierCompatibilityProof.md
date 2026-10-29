# Last-column partial Fourier equivalence: proof

Worker 455 proves the exact published proposition
[`PartialFourierCompatibilityStatement`](PartialFourierCompatibilityStatement.md).
The public theorem is
`Langlands.HarmonicAnalysis.partialFourierCompatibility.{uK}` in
`Langlands.HarmonicAnalysis.PartialFourierCompatibilityProof`. Its type is
exactly `PartialFourierCompatibilityStatement.{uK}`, with no additional
parameters or premises. All other declarations in this proof module are private.

The proposition quantifies over an arbitrary `K : Type uK` with
`[Field K] [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
[BorelSpace K] [LocallyCompactSpace K] [T2Space K]
[TotallyDisconnectedSpace K]`, every unitary additive character `ψ`, every
supplied additive Haar measure `μ`, and every natural `n`. Its only premise
is `IsSelfDual ψ μ`.

Write `M = Matrix (Fin n) (Fin (n + 1)) K` and `V = Fin n → K` in this
explanation. The conclusion provides an actual
`SchwartzBruhat M ≃ₗ[ℂ] SchwartzBruhat M`. Its forward map evaluates to
`partialFourierIntegral ψ μ`, its inverse evaluates to
`partialFourierPlusIntegral ψ μ`, and both displayed last-column integrands
are integrable for every Schwartz input and every matrix. Thus the maps
preserve local constancy and compact support on the whole matrix space.

## Published inputs and conventions

The module imports the target unchanged, the actual proof
[`RowFourierCompatibilityProof`](RowFourierCompatibilityProof.md), and
[`MatrixFourierSliceProof`](MatrixFourierSliceProof.md).
`rowFourierCompatibility ψ μ n hself` supplies both `RowFourierClosed ψ μ n`
and `IsRowSelfDual ψ μ n` from scalar self-duality. In this explanation,

```text
F f y = ∫ u, ψ.complex (rowPairing u y) * f u ∂rowMeasure μ n.
```

Row closure says that `F f` is represented by a row Schwartz function.
Row self-duality says that `F (F f) y = f (-y)` and asserts integrability of
the second-transform integrand. These are proved inputs, not extra
hypotheses of the public theorem. The published row proof obtains scalar
sigma-finiteness from `scalarFourierClosure` and uses
`rowTensorDecomposition`; this module adds no sigma-finiteness instance.

Only the generic `matrixColumns` homeomorphism, `columnProduct`, and its
evaluation lemma are used from `MatrixFourierSliceProof`. The specialized
matrix Fourier slice theorem and its stronger hypotheses are not used.
`rowTensorDecomposition` is available through the row proof's imports.

The coordinates, slices, and raw partial integrals are the published ones in
[`RectangularFourier`](RectangularFourier.md). For `m = [x,y]`,
`rectangularFirstColumns m = x`, `rectangularLastColumn m = y`, and
`rectangularJoin x u = [x,u]`. Define the raw plus transform in this
explanation by

```text
P Φ [x,y] = ∫ u, Φ [x,u] * ψ.complex (rowPairing y u) ∂rowMeasure μ n.
```

The private `pairing_comm` and `pairing_neg` prove symmetry of the finite
dot product and `rowPairing u (-v) = -rowPairing u v`. They reconcile the
argument order of the row and partial integrals.

## Convergence without a product Borel assumption

The private lemma `row_integrable` derives first-transform convergence from
row closure and the convergent second transform. Given a row test `f`, pull
it back under negation to obtain the Schwartz function `fneg(u) = f(-u)`.
Choose a row Schwartz function `g` with `g = F fneg` using closure. Row
inversion applied to `fneg` gives

```text
F g = F (F fneg) = f.
```

The convergence clause of row self-duality applied to `g` now asserts
integrability of `u ↦ ψ.complex (rowPairing u y) * F g u`.
Substitution of `F g = f` gives the required first-transform convergence for
every row Schwartz function `f`.

For a matrix test `Φ` and fixed first block `x`, the published
`rectangularSlice Φ x` is a row Schwartz function. Apply `row_integrable`
to this slice at `y` and at `-y`, respectively. Symmetry, the negation
identity, and commutativity in `ℂ` give the private lemmas
`plus_integrable` and `minus_integrable`. Their integrands are exactly

```text
u ↦ Φ [x,u] * ψ.complex ( rowPairing y u),
u ↦ Φ [x,u] * ψ.complex (-rowPairing y u).
```

Every integral throughout the module remains against the supplied
`rowMeasure μ n`, with its existing finite product measurable structure.
This argument introduces no Borel-space instance on `V` or `M`, no change of
measure, and no additional normalization. In particular, it does not invoke
the bundled raw partial transform whose interface requires a product Borel
instance.

The private `plusLinear` packages the raw plus integral as a complex-linear
map from matrix Schwartz functions into all complex functions on `M`.
Additivity uses `integral_add` with the integrability just proved.
Homogeneity uses `integral_const_mul`.

## Schwartz preservation on the whole matrix space

The private `column_decomposition` pulls `Φ` back through the inverse of
`matrixColumns n (n + 1)`, obtaining a Schwartz function on `Fin (n + 1) → V`.
It applies `rowTensorDecomposition V (n + 1)` and evaluates the resulting
equality in the original matrix coordinates. Thus there are finitely many
coefficients `c j : ℂ` and row tests `g j l` such that

```text
Φ = ∑ j, c j • columnProduct (g j),
columnProduct (g j) m = ∏ l, g j l (fun i => m i l).
```

This use of a coordinate homeomorphism concerns Schwartz functions and
finite products only. It does not transport any integration measure.

For a single column product, `plus_columnProduct` splits the finite product
with `Fin.prod_univ_castSucc`, uses the actual join coordinate identities,
and factors the first-column terms out of the integral. The resulting
formula is

```text
P (columnProduct g) m =
  (∏ l : Fin n, g l.castSucc (fun i => m i l.castSucc)) *
    F (g (Fin.last n)) (rectangularLastColumn m).
```

For each summand choose a row Schwartz partner `k j` for the last factor
`g j (Fin.last n)` using row closure. Replace that factor by `k j`,
retaining the first `n` factors with `Fin.snoc`. The resulting
`columnProduct` is already an element of the whole matrix Schwartz space.
Its published construction proves local constancy by composing each
locally constant factor with the continuous column projection. Its compact
support lies in the inverse image, under `matrixColumns`, of the finite
product of the factors' compact supports. This set is compact. Hence this
step controls all variables together, beyond Schwartz preservation on
individual slices.

The private `plus_closed` combines these transformed column products with
the coefficients `c j`. Linearity of `plusLinear` identifies this finite
sum with the raw plus integral on every matrix. Finally `plusSchwartz`
restricts the codomain of `plusLinear` to the actual Schwartz submodule
using this closure proof. Its evaluation remains definitionally the raw
plus integral. Finite sums and scalar multiples stay in that submodule.

## Inversion and the required equivalence

The private `plus_eq_slice` identifies the raw partial plus integral at
`[x,y]` with `F (rectangularSlice Φ x) y`. For fixed `x`, the slice of
`plusSchwartz Φ` is therefore exactly `F (rectangularSlice Φ x)`.
Applying row inversion to this identity gives `plusSchwartz_twice`:

```text
P (P Φ) [x,y] = Φ [x,-y].
```

Here and below `P` denotes the Schwartz endomorphism `plusSchwartz`, whose
values have the raw integral formula above. Applying this identity twice
and using the published first/last-column join and split identities proves
`plusSchwartz_fourth`, namely `P⁴ Φ = Φ`.

The final theorem constructs a complex-linear equivalence with forward
linear map `P.comp (P.comp P)` and inverse function `P`. Both inverse laws
are exactly `P⁴ = id`; this supplies both compositions required by
`LinearEquiv`. Its inverse evaluation is the raw plus integral by
definition.

For the forward evaluation, `P³ Φ [x,y] = P Φ [x,-y]` follows from the
square identity. The private `plus_reflect` rewrites this last expression
pointwise under the integral using
`rowPairing (-y) u = -rowPairing y u`. It is therefore exactly
`partialFourierIntegral ψ μ Φ [x,y]`, with the required inverse character.
The theorem then supplies `minus_integrable` and `plus_integrable` as the
two convergence clauses.

These clauses quantify over every matrix Schwartz input, so they also
apply to the outputs of either map and give convergence for the iterated
integrals occurring in inversion. The proof works uniformly for `n = 0`:
the tensor decomposition, finite products, `Fin.snoc`, coordinate identities,
and published row inversion all include this case. No positivity premise on
`n`, product Borel premise, second countability, continuity of field
inversion, valuation, or p-adic structure is introduced.

## Source and provenance

The motivating source is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics 105
(1983), 367–464, Section 6.1, printed pages 427–428 (one-based PDF pages
62–63). The registered source is `jpss-1983-rankin-selberg`, at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both scanned pages were visually checked. The registered central-library
pointer lists no erratum; no source-specific erratum file was found in the
checked project and Library errata locations.

At the bottom of page 427 the source writes a matrix in `M(t − 1 × t)` as
`[x,y]` and defines

```text
Φ~[x,y] = ∫ Φ[x,u] ψ̄(ᵗy u) du.
```

Our `n` is `t − 1`. For a unitary character the conjugate character is
`ψ(-rowPairing y u)`, matching the forward integral of the equivalence.
Formula (2) on page 428 defines the twisted action by
`ρ0(g)(Φ~) = (gΦ)~`, presupposing a bijective Schwartz transform.

The explicit equivalence, separate convergence clauses, arbitrary universe
and generic field telescope, and zero-dimensional case are derived internal
packaging supporting that construction, rather than a verbatim theorem of
JPSS. The Lean proof is the column tensor and row inversion argument
described above. This module proves the last-column equivalence only; the
Fourier-conjugated action, covariance formulas, vector-valued Whittaker
integrals, full rectangular Fourier theorem, and gamma/L analytic bases
remain separate units.
