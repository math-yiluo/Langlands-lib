# Twisted symplectic Galois actions and descended involutions

Let `d` be a quasi-split inner-form presentation over a field `K`, and supply
an isomorphism from its model to the split symplectic matrix group with finite
index type `n`. Write `L = d.carrier`. The matrix algebra action of the
adjoint discrepancy value `ξ(1, σ)` is `galoisMatrixHom`. Composing it with
entrywise application of `σ` defines `twistedAction` on `M_(n ⊕ n)(L)`.
The discrepancy cocycle identity, coefficient naturality of the adjoint
action and its composition law prove the semilinear action laws.

The fixed algebra is finite dimensional over `K`. If `n` is nonempty, it is
central and simple by the published general semilinear descent theorems.
The multiplication chart `L ⊗[K] fixed ≃ₐ[L] M_(n ⊕ n)(L)` shows that its
reduced degree is `2 * card n`.

`extendMatrix_chartAlong_galois` proves the overlap identity for this chart
over any commutative `K`-algebra and any coefficient map `L → R`. Tensor
induction reduces it to the defining fixedness equation.

Entrywise Galois application commutes with the standard involution
`x ↦ -J xᵀ J`, as does the adjoint algebra action. Their composition
therefore commutes with it. `descendedInvolution` restricts it to the fixed
algebra, and `descentEquiv_descendedInvolution` proves the intertwining
identity under the multiplication chart. For `n = Fin r`,
`hasStandardSymplecticSplitting` supplies the actual finite Galois field
and chart required by the published splitting predicate.

This is an internal adaptation of the published special-linear twisted-action
construction, using its generic discrepancy values, general algebra descent
and extended chart machinery. The new input is compatibility with the
standard symplectic involution. All assertions retain arbitrary field
characteristic. A comparison with the group scheme of descended norm-one
isometries and the final antihermitian classification remain separate.
