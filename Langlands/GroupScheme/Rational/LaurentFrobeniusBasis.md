# Frobenius orbits and a basis of pointed Laurent functions

This is an internal algebraic continuation of `LaurentAugmentation`. For a
prime `p`, an integer character is called primitive here when it is
nonzero and is not `p` times another integer character. The term refers
only to divisibility by this chosen prime.

Every nonzero character in `I → ℤ` is uniquely `p^r` times a primitive
character. Existence uses a nonzero coordinate: division by `p` strictly
decreases its absolute value, so strong induction terminates. Uniqueness
uses injectivity of multiplication by a nonzero integer and the fact
that a primitive character cannot be divisible by `p`. No finiteness
condition on `I` is used.

Reindexing the coefficient basis from `LaurentAugmentation` gives a basis
indexed by a primitive character and a natural number. In characteristic
`p` its vectors are exactly the iterated Frobenius powers
`(X^m - 1)^(p^r)`. Consequently these powers are linearly independent and
span the augmentation kernel as a module over the coefficient ring.

The construction is motivated by the pointed correction explained in
`LaurentAugmentation.md`, in connection with Springer, *Linear Algebraic
Groups*, second edition (1998), §14.3. The proofs here are direct integer
divisibility and basis-reindexing arguments. They do not yet classify
Frobenius-stable subspaces or assert that a group dominated by a split
torus is split.
