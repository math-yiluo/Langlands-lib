# The right-factor ideal in a tensor product

For an ideal `I` of `B`, `Ideal.rightTensorIdeal R A I` extends `I` along the inclusion of `B` in `A ⊗[R] B`. The definition uses the ordinary image of an ideal under a ring homomorphism.

Over a commutative base ring, tensoring the quotient map `B → B ⧸ I` with the identity of `A` has kernel exactly this extended ideal, for a two-sided ideal `I`. Mathlib computes the kernel after tensoring a surjective map. Specializing to the quotient map identifies its original kernel with `I`.
