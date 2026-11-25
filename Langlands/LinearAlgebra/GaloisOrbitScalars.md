# Scalars transported along a Galois orbit

Internal scalar construction for the fixed-field endomorphism algebra in the
proof that representations of a group of multiplicative type are semisimple and
classified by Galois orbits of characters.

Let a field automorphism group `Aut_k(K)` act on an additive group `X`, through
an integral representation `r`. Fix `χ : X` and its stabilizer `H`.
`orbitValue r χ a` assigns to a point `σχ` the scalar `σa`, using a chosen
automorphism carrying the center to the point; it is zero outside the orbit.
For arbitrary `a : K` the assignment depends on the choices.

`orbitValue_apply` proves that for `a` in the fixed field of `H`, its value at
`σχ` is exactly `σa`, independent of the choice. Indeed, two automorphisms with
the same image of `χ` differ by an element of `H`, which fixes `a`.
`orbitValue_equivariant` then proves equivariance of these scalars on the orbit.

These are direct elementary group-action deductions, with no finiteness,
closedness, separability, or Galois-extension hypothesis. They are an internal
construction, not a statement of the group-scheme representation theorem.
