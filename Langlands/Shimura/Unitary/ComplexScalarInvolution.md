# Harris matrix involutions over complex coefficient rings

This module extends the actual involution comparison of
`ComplexMatrixInvolution` from complex coefficients to an arbitrary
commutative complex algebra. It uses the algebra equivalences constructed
in `ComplexMatrixCoefficients`. All constructions and proofs are internal
consequences of those modules; no involution comparison is assumed as
input.

## Coefficient-linear signature transpose

For a commutative ring `S`, let `H` be the diagonal matrix whose entry at
index `i : Fin n` is `1` if `i.val < r` and `-1` otherwise.
`ComplexMatrix.signatureTransposeOver S n r M` is

\[
 H M^{\mathsf t} H.
\]

`signatureTransposeOver_entry` gives the corresponding signed entry
formula. `signatureTransposeOver_add` and
`signatureTransposeOver_smul` prove additivity and `S`-linearity directly
from matrix multiplication, transposition, and commutativity of `S`.
There is no conjugation of an element of `S` in this operation, and no
involution on `S` is required. The construction works for every `n,r`.

Now assume compatible algebra structures `ℝ → ℂ → S`.
`scalarEquiv_adjoint` proves that the actual scalar extension to `S` of
the real signature adjoint becomes

\[
 (M,N)\longmapsto (H N^{\mathsf t} H, H M^{\mathsf t} H)
\]

under `ComplexMatrix.scalarEquiv S n`. Its proof uses tensor induction.
For `s ⊗ M`, the established scalar-equivalence formula gives matrices
with entries `s * algebraMap ℂ S (M i j)` and
`s * algebraMap ℂ S (star (M i j))`. The adjoint entry formula, conjugation
of the original complex entries, and the real signs identify the two
coordinates; the coefficient `s` stays fixed. Additivity proves the tensor
sum case.

`scalarSignatureInvolution S n r` is the transport of the actual
`signatureAdjoint n r` after scalar extension to `S` along this algebra
equivalence. Consequently it is an `S`-linear, unital, multiplicatively
reversing involution. `scalarSignatureInvolution_apply` proves precisely
the factor-swap formula displayed above by transport and cancellation of
the equivalence.

## Every Harris real place

`harrisScalarMatrixInvolution S n I distinguished` applies the preceding
involution independently at every index of `I`, using `r = n - 1` at the
distinguished index and `r = n` elsewhere. It is an involution on the
function algebra

```
I → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S
```

Its linearity, multiplicative reversal, identity, and involutivity fields
are proved pointwise. The construction itself requires only a decidable
equality on `I`, not finiteness of `I`.

For the Harris specialization, retain the actual totally real number
field `E`, totally complex quadratic extension `K/E`, algebra `A`,
second-kind involution `σ`, the compatible rational scalar structure,
signature charts `C`, and a finite `E`-basis `b` of `A`.
`iteratedScalarMatrixEquiv_involution` identifies
`(σ.rationalInvolution.baseChange ℝ).baseChange S` with
`harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished` under
`C.iteratedScalarMatrixEquiv b S`. The proof uses tensor induction, the
published real-chart involution comparison, and the transported local
matrix involution. Thus the charts are the specified algebra and
signature inputs, and the output involution comparison is proved.

`iteratedScalarSimilitudesEquiv` is the resulting multiplicative
equivalence on actual similitudes. It is obtained from the generic
`AlgebraInvolution.similitudesEquiv` applied to the constructed algebra
equivalence and the proved intertwining equation. Its multiplier theorem
states that the scalar unit is unchanged.

With a rational algebra structure on `S` compatible with `ℚ → ℝ → S`,
`scalarMatrixEquiv_involution` gives the same comparison for direct
rational scalar extension `S ⊗[ℚ] A`. It composes the proved iterated
comparison with `baseChangeTowerEquiv_involution`.
`scalarSimilitudesEquiv` and `scalarUnitaryEquiv` then identify the actual
directly extended similitude and unitary groups with those defined by the
split matrix involution. Their associated theorems prove preservation of
the multiplier and compatibility with the inclusion of unitary points
into similitudes.

## Scope and provenance

The scalar ring may have nilpotents and need not be a field. The new
scalar is always fixed, while conjugation in the tensor calculation acts
on the original complex matrix entries. This is the same ordered split
convention as the imported coefficient equivalence and agrees with the
previous complex-coefficient involution construction.

The module constructs algebra involutions and group equivalences at each
coefficient ring. It does not yet identify these similitude groups with
a product of general linear groups and a multiplicative group, prove a
natural isomorphism of group functors or schemes, or establish smoothness,
reductivity, reflex comparisons, or PEL scheme levels. Those are subsequent
obligations. The actual Harris data and chart choices remain explicit.
