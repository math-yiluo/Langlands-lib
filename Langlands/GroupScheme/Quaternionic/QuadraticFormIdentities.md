# Quaternionic quadratic values and singular subspaces

This internal unit derives elementary identities from the published definitions
in `Quaternionic.Forms`. It uses the left-module row-vector convention and works
over any division algebra with an involution of the first kind, in every
characteristic. No nondegeneracy, quaternionic dimension, or local-field
hypothesis is used.

The linear map `valueSandwich a` on `D / {b - σ(b)}` is induced by
`z ↦ a z σ(a)`. Its well-definedness follows by writing an alternating element as
`b - σ(b)` and conjugating it. The quadratic value of `a • x` is the image of the
value of `x` under this map. In particular a singular vector remains singular
after multiplication by any element of the division algebra.

The shared sesquilinear identities are imported from `Quaternionic.FormLemmas`;
this module adds additivity in the Gram matrix. These finite-sum calculations
show that the polar matrix is hermitian and that a singular vector has zero polar pairing
with itself. Polarization of the quotient-valued quadratic form is
`q(x + y) = q(x) + q(y) + [h_q(x,y)]`. This follows because `a` and `σ(a)`
have the same image in the alternating quotient.

Finally, dimensions of totally singular subspaces form a nonempty set of natural
numbers bounded by the number of row coordinates. Finite-set supremum lemmas
show that the supremum defining the quadratic Witt index is attained. Every
totally singular subspace has dimension at most that index. These are internal
consequences of the frozen definitions and Mathlib finite-dimensional linear
algebra; they add no external mathematical assumption.
