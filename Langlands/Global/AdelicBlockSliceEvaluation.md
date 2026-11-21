# Evaluation at a finite compact point of an adelic block section

This internal construction connects the scalar adelic model to the tensor of the actual inducing realizations. `coefficientFiniteAction` and `coefficientInfiniteCompactAction` are the external tensor actions of the finite adelic and infinite compact block actions, respectively.

At a standard finite compact point `x`, `finiteSlicePoint` is the full compact point `(1,x)`. `finiteSliceEvaluation` takes the normalized Levi slice of a scalar section at this point and applies the inverse of `coefficientEquiv`. Evaluating the resulting tensor by `coefficientEvaluation` recovers the normalized slice.

Given an ambient open level `L`, the coefficient level `finiteSliceLevel` is the inverse image of `L ∩ Kfin` under `d ↦ x⁻¹ embed(d) x`, where `embed` is the finite block diagonal homomorphism. This is an open subgroup because the conjugated embedding is continuous. If `d` lies in this inverse image, put `z = x⁻¹ embed(d) x`. Then `x z = embed(d) x`, and `embed(d)` lies in `Kfin` since `x` and `z` do. Right translation by `z` fixes an `L`-fixed section; the normalized slice formula identifies it with the coefficient action of `d`, with the half character equal to one on the compact parabolic. Thus evaluation preserves fixed vectors at the stated levels.

For the infinite compact action, the image of a block compact element is in the ambient infinite compact. Its adelic inclusion commutes with `(1,x)`, giving the same slice formula with trivial half character. This proves equivariance along the block diagonal compact inclusion. The present module proves the two evaluation laws, not yet that finitely many evaluations separate the multiplicity maps.
