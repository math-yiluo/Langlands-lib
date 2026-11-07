# Character embedding for a rank-one segment

This internal specialization starts with an actual smooth representation of
`GL₁` acting by `χ ∘ det`, where `χ` has open kernel. It constructs an injective
intertwiner into the actual normalized increasing induction with factors
`χ, νχ, …, ν^(m−1)χ`.

The source has the indexed tensor carrier of those factors and scalar action
by the midpoint character `ν^((m−1)/2)χ ∘ det`. No dimension or irreducibility
assumption is made in this construction.

The proof computes the tensor action on pure tensors and extends by their
spanning property. The published block determinant formula and the
`RankOneSegmentModulus` half-modulus cancellation show that the full normalized
parabolic action is the restriction of the midpoint character. Its kernel is
open because it contains the intersection of the two open factor kernels.
The intertwiner is constructed directly on the actual segment induction by
the functions `g ↦ φ(g) • v`. Multiplicativity proves covariance and
intertwining with right translation; the open character kernel fixes the
entire function. Evaluation at the identity proves injectivity.
