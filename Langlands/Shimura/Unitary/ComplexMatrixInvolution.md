# Complex matrix coordinates for the Harris involution

This module identifies the actual scalar-extended Harris involution in the
ordered two-factor matrix decomposition. It constructs the corresponding
isomorphisms on complex unitary and similitude points. It is an internal
consequence of `ComplexMatrixSplitting`, the published real involution
comparison, and the tensor-tower comparison.

## Inputs and convention

`AlgebraInvolution.transport` is generic over a commutative base ring `R`, two
possibly noncommutative `R`-algebras, an algebra involution on the first, and an
`R`-algebra equivalence to the second. It transports the involution by
`e ∘ σ ∘ e⁻¹`. Its linearity, unitality, reversal of multiplication and
involutivity follow from these properties of the inputs. `transport_equiv`
proves the intertwining identity.

For the matrix constructions, `n` and `r` are arbitrary natural numbers. Put
`H = signatureMatrix n r`, the diagonal matrix with entry `+1` for `i < r`
and entry `-1` otherwise. The same formulas remain valid when `r > n`.
`signatureTranspose n r` is the complex-linear operation

\[
 T(M)=H M^t H.
\]

It does not conjugate entries. By comparison the original real signature
adjoint is `H conjugate(M)^t H`. The complex tensor decomposition is the
ordered one `z ⊗ M ↦ (z M, z conjugate(M))`; new complex scalars are fixed by
the scalar-extended involution.

## Split involution

`signatureTranspose_entry` and `signatureAdjoint_entry` prove the entry formulas

\[
 T(M)_{ij}=\epsilon_i M_{ji}\epsilon_j,\qquad
 \sigma_H(M)_{ij}=\epsilon_i\overline{M_{ji}}\epsilon_j,
\]

where `ε_i` is the indicated real sign. The transpose operation preserves
addition and complex scalar multiplication, as proved in the two accompanying
lemmas.

`complexEquiv_adjoint` proves, for every element of
`ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ`, that the scalar-extended signature adjoint
acts on its two matrix coordinates by

\[
 (P,Q)\longmapsto (T(Q),T(P)).
\]

The proof is tensor induction. On a pure tensor it uses the ordered splitting
formula and the two entry formulas, with a case split on the real signs. The
additive step uses the additivity of the constructed maps.

`splitSignatureInvolution n r` is an actual `AlgebraInvolution ℂ` on the product
of matrix algebras. It is obtained by transport along `complexEquiv`.
`splitSignatureInvolution_apply` proves its explicit swap-and-transpose formula
for every pair `(P,Q)`, using surjectivity of that algebra equivalence. Thus the
formula is established for all pairs, not merely images of pure tensors.

`harrisComplexMatrixInvolution n I distinguished` constructs the pointwise
product of these complex involutions, with `r = n-1` at the distinguished index
and `r = n` elsewhere. Its scalar ring is `ℂ` and its algebra is the actual
function ring of matrix pairs. The required involution laws are proved
pointwise.

## Comparison with the actual Harris algebra

The `HarrisSignatureCharts` section retains the same hypotheses as
`ComplexMatrixSplitting`: the totally real/totally complex quadratic number
field input, the indicated algebra structures and rational scalar tower, a
second-kind involution, actual Harris charts `C`, and a finite `E`-basis `b` of
`A`. No complex involution comparison is added as an assumption.

`iteratedComplexMatrixEquiv_involution` proves that the actual involution on
`ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)` is carried to `harrisComplexMatrixInvolution`. Tensor
induction reduces this to the published `realMatrixEquiv_involution` and the
matrix-factor comparison. `complexMatrixEquiv_involution` then proves the
same result directly on `ℂ ⊗[ℚ] A`, using the published compatibility of the
tensor-tower equivalence with involutions.

`complexSimilitudesEquiv` and `complexUnitaryEquiv` restrict this genuine algebra
isomorphism to the groups defined by their involution equations. The former
preserves the common scalar multiplier, as proved by
`complexSimilitudesEquiv_multiplier`. `complexUnitaryEquiv_inclusion` proves
that the two comparisons agree under inclusion with multiplier one. These
constructions reuse `AlgebraInvolution.similitudesEquiv` and `unitaryEquiv`,
whose intertwining hypothesis is discharged by the comparison just proved.

## Provenance and remaining scope

All constructions and proofs are internal algebraic consequences of the imported
matrix splitting, real signature comparison, and generic transport of unitary
and similitude groups. No additional external theorem is invoked.

The resulting group isomorphisms concern complex points of the actual tensor
algebras. This module does not identify the represented complex group schemes
with products of general linear groups, prove smoothness or reductivity,
compute cocharacter weights, or prove independence of the charts and basis.
Cocharacter conjugacy, reflex-field comparison, PEL geometry, representability,
level schemes and coefficient descent remain separate host-task obligations.
