# Actual product pullbacks with constant identity slices

This internal adapter packages the tensor-coordinate support step for an
actual pointed equivariant scheme morphism `f : V ⊗ W ⟶ Z`. It is derived
for the coordinate-tensor argument in Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), Lemma 3.3.4,
printed pp. 108–109 / PDF pp. 134–135.

Let `k : Type u` be a field and let `a`, `b`, and `c` be actual pointed
actions of the commutative group scheme `S` on affine schemes `V`, `W`,
and `Z` over `k`. `tensorPullback f` is the actual pullback on coordinate
algebras followed by the actual product coordinate equivalence
`tensorCoordinates`. Its injectivity follows from injectivity of the
actual pullback. Under pointed equivariance, it sends a weight function
on `Z` to the same character's actual tensor weight space. The weight
conditions retain every coefficient algebra and every point.

`support_subset_sum_of_injective_constant_slices` assumes injectivity of
the actual pullback and two algebra-map equalities. Each says that
evaluating one tensor factor at its distinguished point reduces the
pullback to evaluation at the distinguished point of `Z`, followed by
the scalar inclusion into the other factor. It also assumes internal
direct-sum decompositions of the two augmentation eigenspace families
and of the actual product coordinate eigenspace family.

The proof takes a nonzero augmentation eigenfunction on `Z`. Injectivity
keeps its tensor pullback nonzero, and equivariance preserves its weight.
Each constant-slice equality and the augmentation condition kill one
identity slice. The tensor support theorem then forces the character
into `Set.image2 (· + ·) (support a) (support b)`.

No zero character is adjoined. The decomposition assumptions and slice
equalities remain explicit obligations for a consumer, and this file
does not prove the image-specific hypotheses, the Lie-weight comparison,
or the complete `SemigroupCommutatorStatement`.
