# Representation semisimplicity of split-torus tangent vectors

For every field `k : Type u`, every actual split torus `T` over `k`, and every
`X : lieKernel T k`, the proposition
`Langlands.GroupScheme.Lie.SplitTorusSemisimpleStatement.{u}` asserts
`IsSemisimpleElement T X`. The theorem `splitTorusSemisimpleStatement`
proves it at arbitrary universe `u`.

Here `lieKernel` is the kernel of reduction of actual dual-number points.
`IsSemisimpleElement` tests every algebraic group-scheme representation
`T ⟶ GL_(Fin n)`: the extracted tangent matrix, after extension from `k`
to `AlgebraicClosure k`, must define a semisimple endomorphism. The result
has no characteristic, perfection, infinitude, or positive-rank premise.
Rank zero and representations of dimension zero are included.

The stronger helper `isSemisimpleElement_targetMap_splitTorus` proves
semisimplicity of the image of any tangent vector under any homomorphism
from a standard split torus to an arbitrary target group scheme `G`.
Neither closedness nor centrality of that homomorphism is assumed.
For an abstract split torus the main theorem, followed by
`IsSemisimpleElement.map`, gives the same image conclusion.

## Implemented proof

The proof reuses the actual representation weight matrices
`CharacterRestrictionFiniteIndex.weight`, their finite `weightSupport`,
the evaluation formula `affinePointsEquiv_eval`, and the orthogonal
idempotent identity `weight_mul_weight`. These published lemmas apply
without centrality to any representation restricted along a standard
split-torus homomorphism.

An idempotent endomorphism is annihilated by `X (X-1)`. The two factors
are coprime over any field, including characteristic two, and the polynomial
is separable. Mathlib's squarefree annihilator criterion gives
semisimplicity. Applying this after extension to the algebraic closure proves
`isGeometricallySemisimpleMatrix_of_idempotent`.

The finite-sum lemma `isGeometricallySemisimpleMatrix_sum` proceeds by
induction on a finite set. Entrywise scalar extension and `Matrix.toLinAlgEquiv'`
preserve commutation and addition, so Mathlib's
`Module.End.IsSemisimple.add_of_commute` proves the induction step over
the algebraic closure.

For a tangent point `X` of the standard split torus, apply the actual
evaluation formula to its dual-number unit coordinates. Taking epsilon
coefficients entry by entry gives
`tangentMatrix_splitTorus_weight_sum`: the target tangent matrix is
the finite sum of the weight matrices, each scaled by the epsilon
coefficient of its corresponding monomial value at `X`.
No assertion about surjectivity of a differential is used.

Orthogonal idempotents commute. Scalar multiples preserve both their
geometric semisimplicity and their commutation, so the finite-sum lemma
proves `isGeometricallySemisimpleMatrix_sum_weight`. Applying it to the
coefficients just extracted proves semisimplicity in every target
representation. Finally, an isomorphism from an abstract split torus
to a standard split torus and its inverse transport the actual kernel
point; their composite is the identity. This proves
`isSemisimpleElement_of_isSplitTorus` and the global proposition.

## Provenance and scope

This is a derived result from the published weight-projector and actual
dual-number interfaces, together with Mathlib's semisimple-endomorphism
lemmas. It introduces no external structural assertion. It supplies a
torus tangent input for the Cartan-generation development; it does not
prove the structural isogeny reduction or the final Cartan-generation
statement.
