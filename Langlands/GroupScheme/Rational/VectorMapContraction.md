# Coefficient contraction of vector-valued regular maps

This internal construction extends the published coefficient retraction in
`Rational.TorusVectorCocycle` from rational vectors to regular maps with values
in a vector group. It is intended to support descent of linear cochain equations.

Let `k ⊆ K` be any extension of fields in universe `u`, let `H` be an affine
group scheme over `k`, and let `V` have supplied natural vector coordinates of
dimension `d`. Given an arbitrary morphism of relative schemes
`b : H_K.X ⟶ V_K.X`, `contractedMap` constructs a morphism `H.X ⟶ V.X`.
The input and output are regular maps; no homomorphism law is assumed.

On a `k`-algebra `A`, extend a point of `H(A)` to `A ⊗[k] K`, apply `b` using
the actual pullback-point comparison, take the supplied vector coordinates,
and apply `VectorCocycleDescent.contract` coordinatewise. This contraction
uses a chosen `k`-linear retraction `K → k` which fixes `1`.

`tensorMap` extends an arbitrary coefficient map while fixing `K`.
`contract_naturality` follows by tensor induction. Naturality of the actual
pullback-point comparison and of the supplied coordinates then proves
naturality of the contracted vector points. Evaluating this family at an
affine presentation of `H` defines the actual map. `comp_contractedMap`
identifies its evaluation on every affine test with the explicit formula.

The construction uses no field finiteness, separability, perfection or
characteristic assumption. It is not a descent datum for the input map:
contraction may change it after scalar extension. No cocycle identity,
extension splitting or torus lift-existence theorem is asserted here.
