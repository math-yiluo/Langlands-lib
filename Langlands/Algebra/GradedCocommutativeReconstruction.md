# Reconstruction of graded cocommutative Hopf algebras

Internal supporting construction for the proof that extensions of groups of
multiplicative type over a field are of multiplicative type.

Let `K` be an algebraically closed field and `A` a commutative, cocommutative
Hopf algebra over `K`. Let `N` be any commutative group and let
`π : A →ₐc[K] K[N]` be surjective. Suppose the degree-zero part of its
`N`-grading lies in the linear span of the group-like elements of `A`.

The definition `Langlands.GroupAlgebraCoaction.groupAlgebraEquiv` constructs
an actual bialgebra equivalence

```text
A ≃ₐc[K] K[Additive (GroupLike K A)].
```

No finite generation or smoothness hypothesis is assumed. The field,
Hopf-algebra carrier and grading-group universes are independent.

The implemented construction first applies
`GroupAlgebraCoaction.span_isGroupLikeElem_eq_top` from
[`CocommutativeGradedGroupLike`](CocommutativeGradedGroupLike.md).
That theorem proves that the group-like elements span `A`, by finding a
common translation eigenvector in each nonzero homogeneous component and
reducing each component to degree zero by an invertible group-like element.
The published `MonoidAlgebra.bialgEquivOfSpanGroupLike` reconstructs `A`
from the multiplicatively written group of group-like elements. Taking its
inverse and then `MonoidAlgebra.toAdditiveBialgEquiv` gives the displayed
equivalence in the additive group-algebra convention used by diagonalizable
groups.

This is an internal combination of the graded-spanning proof of
`CocommutativeGradedGroupLike` and the published group-like reconstruction API
(`GroupLikeReconstruction`). This definition supplies a data-valued entry point for
that graded-spanning result.
