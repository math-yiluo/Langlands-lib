# Intermediate point norms at a quadratic extension

`QuadraticIntermediateNormStatement` computes the class of the intermediate
point norm of an affine commutative group scheme over a field `F`. Let `E/F`
be finite Galois, let `N` be an intermediate field, and let `M` extend both `E`
and `K` over `F`. For a `K`-automorphism `σ` of `M` with `σ * σ = 1`, the
quotient used here is the group of `M`-points modulo the image of the
homomorphism `r ↦ r * σ(r)`. Two points have the same class exactly when one is
the other times such a product.

The image of the `N/F` point norm in this quotient is the product of the classes
indexed by the embeddings `N →ₐ[F] E` fixed by the restriction of `σ` to `E`.
The proof applies the intermediate point norm formula in `M`. Composition with
the restricted automorphism permutes the embeddings, and equivariance
identifies the factors of each two-element orbit as `r` and `σ(r)`. The finite
involution product lemma removes these orbit products in the quotient.

Two auxiliary facts prepare the use at real completions. For a quadratic
Galois extension `M/K` and `σ ≠ 1`, an embedding fixed pointwise by `σ` factors
through `K` by the fixed-field theorem. If `K` is equipped with a ring
isomorphism to `ℝ`, a unit that is positive at an embedding into `K` has a
square root in `K`. Naturality of cocharacter evaluation then identifies its
image in `M` as a product of a point from `K` with its conjugate. A negative
unit is `-1` times a positive unit, so its evaluation has the class of the same
cocharacter evaluated at `-1`.

This is an internal calculation for the real-place approximation argument. It
derives the point norm formula in the quotient from the intermediate norm,
the finite involution product, and the real square-root and sign identities.
