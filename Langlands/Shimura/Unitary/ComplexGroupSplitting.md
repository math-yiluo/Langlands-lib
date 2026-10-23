# Harris similitudes over complex coefficient algebras

This module constructs a multiplicative equivalence from the actual scalar
extension of the rational Harris similitude group to a product of matrix
unit groups and one scalar unit group. It is an internal consequence of
the actual matrix and involution comparisons in `ComplexScalarInvolution`
and the explicit exchange-similitude equivalence in `ExchangeInvolution`.
No group-splitting equivalence is assumed as input.

## The matrix involution

Let `S` be a commutative ring with compatible algebra structures
`ℝ → ℂ → S`. Write `H_r` for the diagonal matrix with `1` at indices
less than `r` and `-1` at the other indices. The existing operation
`signatureTransposeOver S n r` is `M ↦ H_r Mᵗ H_r`.
`signatureTransposeInvolution` makes this operation an actual
`S`-algebra involution. Its additivity and linearity use the established
matrix identities. Preservation of one, reversal of multiplication and
involutivity follow by projecting the corresponding identities for
`scalarSignatureInvolution`; the latter exchanges two matrix factors.
This construction fixes every coefficient of `S`.

For a type `I` with decidable equality and an index `distinguished`,
`harrisTransposeInvolution` applies this involution at every index, with
`r = n - 1` at the distinguished index and `r = n` elsewhere. Each of
its required identities is proved pointwise. Neither finiteness of `I`
nor positivity of `n` is needed for these auxiliary definitions.

`familyPairEquiv` is the actual algebra equivalence

```
(I → M_n(S) × M_n(S)) ≃ₐ[S] ((I → M_n(S)) × (I → M_n(S))).
```

It takes a family of ordered pairs to its two coordinate families, with
inverse given by pairing at each index. The inverse and algebra laws are
proved by reduction. `familyPairEquiv_involution` proves that this map
intertwines `harrisScalarMatrixInvolution` with the exchange involution
of `harrisTransposeInvolution`. Each coordinate is the established
swapped signature-transpose formula.

## The explicit split group

`ComplexMatrix.harrisSimilitudesEquiv` constructs

\[
 \operatorname{GU}_{\mathrm{split}}(S)
 \simeq \left(\prod_{\tau\in I}\mathrm{GL}_n(S)\right)\times S^\times.
\]

Here `GL_n(S)` means the actual unit group of the square matrix ring,
and the source is the existing similitude subgroup with the scalar
multiplier retained as part of each element. The construction composes
three proved multiplicative equivalences: transport by
`familyPairEquiv`, the exchange-similitude equivalence, and the
pointwise-units equivalence. Both inverse laws and preservation of
multiplication are therefore supplied by these constructions.

The projection lemmas identify the forward map as the first matrix at
each index together with the original scalar multiplier. If the target
is `(a,c)`, `harrisSimilitudesEquiv_symm_second` identifies the second
matrix of the inverse at `τ` as

\[
 (c\,1_n)\,H_{r_\tau}(a_\tau^{-1})^{\mathsf t}H_{r_\tau}.
\]

This is an inverse in the matrix unit group, with `c` mapped by the actual
scalar algebra map. In particular the second coordinate is constructed,
not supplied with an assumed similitude relation. No complex conjugation
of `c` or of matrix entries in `S` occurs.

## Actual Harris scalar extensions

Retain the imported `HarrisSignatureCharts C` data: a totally real number
field `E`, its totally complex quadratic extension `K`, the algebra `A`
with second-kind involution `σ`, the compatible rational scalar
structure, the chosen signature charts, and a finite `E`-basis `b` of
`A`. The signature and chart hypotheses remain explicit inputs.

`C.iteratedScalarGroupSplitting b S` constructs

\[
 \operatorname{GU}_{(\sigma_{\mathbb Q}\otimes\mathbb R)\otimes S}
 \simeq
 \left(\prod_{\tau:E\to\mathbb R}\mathrm{GL}_n(S)\right)\times S^\times.
\]

Its construction composes `iteratedScalarSimilitudesEquiv` with the
split-matrix equivalence above. The matrix projection theorem identifies
the first coordinate with the first matrix of
`C.iteratedScalarMatrixEquiv b S` applied to the underlying algebra
unit. Its multiplier theorem identifies the second coordinate with the
original multiplier.

When `S` also has a rational algebra structure compatible with
`ℚ → ℝ → S`, `C.scalarGroupSplitting b S` similarly gives the
multiplicative equivalence for the direct scalar extension `S ⊗[ℚ] A`.
Its matrix and multiplier projection theorems give the same formulas
using `scalarMatrixEquiv`. Finally `scalarGroupSplitting_tower` proves
that the direct and iterated splittings agree through the actual
`baseChangeTowerSimilitudes` equivalence. Equality of the matrix-unit
values and of the multipliers proves this identity.

## Provenance and remaining scope

All results here are internal algebraic consequences of the imported
constructions, proved by explicit maps, coordinate identities and
composition. The actual Harris specialization is retained, including its
chart choices; an arbitrary output group equivalence is never stored as
input. The results apply to commutative complex coefficient rings with
nilpotents as well as fields, and they do not require faithfulness or
nontriviality beyond the displayed hypotheses.

This module constructs group equivalences at each coefficient algebra.
Naturality in that algebra, a resulting isomorphism of group schemes,
smoothness and reductivity, and the PEL moduli and scheme-level
constructions remain subsequent obligations.
