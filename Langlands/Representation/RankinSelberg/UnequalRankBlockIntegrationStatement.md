# Block matrices and integration helpers for unequal-rank JPSS integrals

This module states nine helper propositions in
`Langlands.RankinSelberg.AdjacentBlockReduction` and defines their conjunction
`UnequalRankBlockIntegrationStatement`. Every component is a `Prop`-valued
definition quantifying the complete telescope of its source theorem, including
implicit carrier types, instances and hypotheses used by the source proof.
The aggregate has independent universe parameters `uX`, `uP`, `uG`, `uF`, `uV`
in that order and has no mathematical parameter or additional premise. The
components use the relevant subset of these universes.

This is a derived internal statement package. It isolates the ready matrix,
finite coefficient integration and row Fubini interfaces from Worker 180's
shared adjacent-block draft, revision 11 of task
`798cefd9-ab16-4562-ab1a-085680064306`. The source pair is
`Langlands/Representation/RankinSelberg/UnequalRankBlockSpanProof.lean` and
its Markdown in shared revision
`revision-11-bdc9755f26661654885ff0567c2254dde91cbe61d4449ae448ada9bf4b058b63`.
Its proofs are not copied into this module. A subsequent proof is intended
to have name `unequalRankBlockIntegration` and export each helper under its
original source name and telescope.

## Published constructions and conventions

The module imports the published pairs `UnequalRankBlockMatrix`,
`FunctionalEquationStatement` and `RowFourier`, together with Mathlib's
product-integral API. `QuotientIntegrals`, imported by the first two pairs,
supplies `unequalRankMatrix`, `rectangularUnipotent`, `rectangularMeasure`,
the quotient and the underlying integrals. `blockMatrixAt` is imported from
`UnequalRankBlockMatrix`; it only transports the natural-number rank along
`hr : r = n + (j + k + 1)`. `unequalRankIntegralAt` is the corresponding
existing integral wrapper from `FunctionalEquationStatement`.

For a field `F`, a smaller matrix `g` in `GL_(n+1)` and a rectangle `Y` with
`j` rows and `n+1` columns, the actual unequal-rank matrix is

```
[ g  0    0       ]
[ Y  I_j  0       ]
[ 0  0    I_(k+1) ]
```

Its rank is `n + (j + k + 1) + 1`. In the fixed-rank wrappers it is `r + 1`.
Thus the source's smaller rank `t` is Lean `n + 1`, and its larger rank is
Lean `r + 1`. The final identity block always has size `k + 1`. All natural
numbers in the component statements may be zero subject to their displayed
rank equations: `n = 0` gives smaller rank one, and `j = 0` gives an empty
rectangular block.

`rowMeasure ν t` from `RowFourier` is the actual finite product of the supplied
scalar `AdditiveHaarMeasure ν`; `rectangularMeasure ν j t` is the product of
`j` such row measures. Empty products have unit point mass. No normalization
is chosen. The continuity and rectangular-measure conventions agree with the
published `UnequalRankFiniteExpansionProof`, `RowFourier` and
`QuotientIntegrals` pairs. No unfinished adjacent-span module is imported.

## Component statements

The conjunction has the following order.

1. `CoefficientFiberIntegralStatement` is the universally quantified type of
   `exists_coefficient_fiber_integral`. Let `X : Type uX` be a topological
   measurable space with measurable open sets, `P : Type uP` an arbitrary
   parameter type, and `G : Type uG` a topological group. Let
   `V : Type uV` be an additive commutative group and complex module,
   `ρ : Representation ℂ G V` smooth, `N` a subgroup and `θ : N →* ℂˣ`.
   For a supplied measure `μ` finite on compact sets, a functional
   `ℓ : functionals N θ ρ`, a continuous `U : X → G`, a family `B : P → G`,
   and a coefficient `f` in `coefficientModel ρ ℓ`, assume
   `HasCompactSupport (fun x p => f.val.val (B p * U x))`.
   Then there exists one `f₀` in the same model such that for every `p`
   the scalar function `x ↦ f(B(p)U(x))` is `Integrable` against `μ` and
   `f₀(B(p))` equals its integral. The existential coefficient precedes
   every `p`. Compact support is uniform in the whole parameter family.
   There is no topology on `P` or `V`, and no completeness assumption on `V`;
   the integrals are complex-valued.

2. `UnequalRankMatrixSnocStatement` is the type of `unequalRankMatrix_snoc`.
   For any field, dimensions `n,j,k`, smaller matrix `g`, preceding rows
   `Y` and final row `x`, it asserts
   `unequalRankMatrix (j+1) k g (Fin.snoc Y x)` equals
   `unequalRankMatrix (j+1) k g (Fin.snoc Y 0)` multiplied on the right by
   `rectangularUnipotent (j+1) k (Fin.snoc 0 x)`. Only the field instance
   is quantified; no topology or representation carrier is present.

3. `BlockMatrixAtEntryStatement` is the type of `blockMatrixAt_entry`.
   For any field and the original binder order `n,r,j,k,hr,g,Y,a,b`, its
   conclusion gives exactly the sum of the diagonal-inclusion entry and
   rectangular entry. The first is `g(a,b)` in the leading `(n+1)` square,
   zero in its remaining columns, and the Kronecker delta in the remaining
   rows. The second is `Y(a-(n+1),b)` when
   `n+1 ≤ a < n+1+j` and `b < n+1`, and zero otherwise. The dependent
   finite indices and inequalities are those in the source formula.

4. `BlockMatrixAtSnocZeroStatement` is the type of `blockMatrixAt_snoc_zero`.
   Over any field, it retains both equations
   `h₁ : r = n + ((j+1) + k + 1)` and
   `h₂ : r = n + (j + (k+1) + 1)`. It states that
   `blockMatrixAt (j+1) k h₁ g (Fin.snoc Y 0)` equals
   `blockMatrixAt j (k+1) h₂ g Y`. The equality compares actual matrices
   in the same group `GL_(r+1)`.

5. `ContinuousLastRowUnipotentStatement` is the type of
   `continuous_lastRowUnipotent`. For a field with a supplied topology
   making it a topological ring and arbitrary `n,j,k`, the actual map
   `x ↦ rectangularUnipotent (j+1) k (Fin.snoc 0 x)` is continuous on
   `Fin (n+1) → F`.

6. `RectangularLastRowMeasurePreservingStatement` is the type of
   `rectangular_lastRow_measurePreserving`. It quantifies only
   `[AddGroup F]`, `[TopologicalSpace F]`, `[MeasurableSpace F]`, a supplied
   `ν : AdditiveHaarMeasure F`, `[SigmaFinite ν.measure]` and `j,t`.
   The actual `MeasurableEquiv.piFinSuccAbove` at `Fin.last j` preserves
   measure from `rectangularMeasure ν (j+1) t` to
   `(rowMeasure ν t).prod (rectangularMeasure ν j t)`. The selected
   last row is the first component and the preceding rows the second.
   No field, scalar Borel or topological-group instance is added.

7. `RectangularIntegralLastRowStatement` is the type of
   `rectangular_integral_lastRow`. With the same telescope as item 6,
   followed by a complex-valued function on `(j+1) × t` rectangles and
   its explicit `Integrable` hypothesis, the rectangular integral equals
   the integral over earlier rows `Y` of the integral over the final
   row `x` of `f (Fin.snoc Y x)`. The inner measure is `rowMeasure ν t`
   and the outer measure is `rectangularMeasure ν j t`. This is a
   genuine Fubini target; the integrability premise is retained.
   Both `j = 0` and `t = 0` are included.

8. `BlockCoefficientIntegrableStatement` is the type of
   `blockCoefficient_integrable`. Its ambient telescope is a field `F`
   with a topology, `[IsTopologicalRing F]` and a measurable space,
   followed by the algebraic complex carrier `V`. Then come the
   supplied additive Haar `ν`, its sigma-finiteness, `n,j,k` and
   `[BorelSpace (Matrix (Fin j) (Fin (n+1)) F)]`. For a unitary additive
   character `ψ`, a smooth representation `π` of
   `GL_(n+(j+k+1)+1)`, a functional `ℓ`, a coefficient `f` and a
   supplied compact rectangular set `C`, assume
   `∀ g X, f.val.val (unequalRankMatrix j k g X) ≠ 0 → X ∈ C`.
   For every smaller-group argument `g`, the rectangular scalar
   coefficient is genuinely `Integrable` against
   `rectangularMeasure ν j (n+1)`. The same `C` works for every `g`.
   Its existence is not asserted. The exact telescope includes the
   matrix-space Borel instance and includes neither `[T2Space F]`
   nor `[BorelSpace F]`.

9. `UnequalRankIntegralAtEqOuterStatement` is the type of
   `unequalRankIntegralAt_eq_outer`. It quantifies a field with a
   topology and measurable space, `n,r,j,k,hr`, a measurable space on
   `LeftUnipotentQuotient n F`, the character `ψ`, absolute value `abv`,
   arbitrary measures `μ` on that quotient and `ν` on the rectangle,
   actual `WhittakerFunctions ψ r` and `InverseWhittakerFunctions ψ n`,
   and `s : ℂ`. The fixed-rank integral is the outer integral against `μ`
   whose integrand, evaluated at a quotient point `q`, is
   the integral of `f(blockMatrixAt j k hr q.out X)` against `ν`,
   multiplied by `f'(q.out)` and by
   `determinantWeight abv q.out (s - ((j+k+1 : ℕ) : ℂ) / 2)`,
   in that order. This is an equality of the existing totalized
   iterated integrals. It adds no convergence, sigma-finiteness,
   Haar, support or Fubini premise, uses no interchange in the
   quotient variable and requires no topological-ring instance.

## Provenance and scope

The original motivation is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464,
source `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 393–395 (one-based PDF pages 28–30) treat unequal ranks
in Theorem (2.7), using rectangular block integrals and finite sums
of translates. The unnumbered lemma on pp.394–395 supplies the support
and Fourier comparison used to relate adjacent `j`, and p.395 gives
the chain of ideal inclusions. These pages were read visually in the
retained original.

The cited predecessor is the same authors' *Automorphic Forms on GL(3) I*,
Ann. of Math. (2) 109 (1979), 169–212, source `jps-1979-gl3-i`,
SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed pages 188–190 (one-based PDF pages 21–23), read in text and images,
contain the block integrals (4.1.1)–(4.1.3), Proposition (4.1.4) and
Lemma (4.1.5), with the finite-translates argument and adjacent ideal
inclusions on p.190.

The complete telescopes here are internal derived formulations from
Worker 180's draft using the published concrete APIs. In particular,
the rank transport, general algebraic coefficient-fiber package,
product-coordinate measure change and totalized outer-integral identity
are not claimed to occur verbatim in either original. Finite algebraic
coefficient integration is motivated by the finite-translates arguments;
the row measure and integral statements express the corresponding
finite-product change of coordinates. The package assumes compact
support where specified and states no support-existence theorem,
Fourier-existence theorem, block-span equality, analytic continuation
or functional equation. This module defines proposition targets and
supplies none of their proofs.

Worker 180 authored the reused helper statements and source design.
Worker 52 extracted their full telescopes into these proposition
definitions and wrote this documentation.
