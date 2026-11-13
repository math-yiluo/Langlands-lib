# Powers in square-zero coefficient kernels

This internal construction encodes an actual affine group-scheme point that
reduces to the identity as a point over the algebra of congruent coefficient
pairs. Its first projection is the identity and its second projection is the
original point.

`affineKernelPairsPoint` is defined for an affine group scheme over an arbitrary
commutative base ring in universe `u`, an algebra map `f : A →ₐ[R] B`, and an
actual point `x` with `affineMap G f x = 1`. It uses the ideal `RingHom.ker f`;
this constructor itself does not require that ideal to be square-zero.

The square-zero scaling maps on pairs add according to the group law. The proof
compares points over triples by their two projections to congruent pairs, which
jointly determine all three coefficients, then applies
the sum map. Induction shows that scaling by a natural number is the corresponding
power. Consequently, if that natural number annihilates the coefficient kernel,
it also annihilates the group-valued identity kernel. Precisely,
`affineKernel_pow_eq_one` assumes `(RingHom.ker f) ^ 2 = ⊥` and
`∀ a ∈ RingHom.ker f, (n : A) * a = 0`, and proves `x ^ n = 1` for every
point with `affineMap G f x = 1`.

The construction and proof use the published congruent-pair algebras and
square-zero scaling maps from `AlgebraicGeometry.InfinitesimalKernel`, together
with the actual affine-point coordinate equivalence and joint injectivity. No
smoothness, field characteristic, or unit hypothesis is imposed. This is an
internal ingredient for successive congruence quotients in mixed characteristic.
