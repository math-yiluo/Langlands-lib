# Actual roots of the standard rank-one cover

This internal proof development computes a property of the actual adjoint
roots of the product of `SL₂` with a split commutative torus `C`. It does not
construct a cover of an arbitrary reductive group.

First, the kernel of the first projection `H × C ⟶ H` is central on every test
scheme and after every test-scheme restriction. The proof uses the actual
product-points equivalence. The first coordinate is the identity for a point
in the kernel, and multiplication of the second coordinates commutes because
`C` is a commutative group scheme.

The published nonzero-weight injection for homomorphisms with central full
kernel then sends each root of `SL₂ × C` to a root for its action on `SL₂`.
The torus-action restriction theorem identifies that root with the pullback of
a root for the standard diagonal torus of `SL₂`.

More generally, `exists_root_of_mem_roots_tensor_comm` applies to an affine,
locally finite type group `H` and a split torus acting on `H`, with a split
commutative product factor `C` and an affine, locally finite type product.
The construction `rootOfTensorComm` chooses an actual first-factor root from
this existence result for each actual product root. The return type includes
both membership in the first-factor root set and the equality asserting that
character pullback along the first projection gives exactly the original
root. This is a choice of a root witness; no root-subgroup parametrization is
constructed.

The published matrix computation `SpecialLinear.FinSucc.exists_coord_of_mem_roots`
says that such an `SL₂` root has coordinates `w(p) - w(q)` for distinct indices
`p, q : Fin 2`. Exhausting these indices gives equality or opposition for any
two roots. Pullback preserves negation, so any two actual roots of `SL₂ × C`
are equal or opposite as well.

The provenance is this direct internal combination of actual product points,
the central-kernel nonzero-weight injection, the split-torus restriction
formula, and the explicit special-linear matrix calculation. There is no
root-datum or reducedness assumption. The affine and finite-type instances in
the product lemmas are explicit ambient scheme hypotheses and will be
discharged from the split-torus and `SL₂` geometry by the cover consumer.
The product calculation imports no proposed central-cover statement.
