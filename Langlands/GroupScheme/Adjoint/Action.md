# Automorphic actions on actual full-centre quotients

This internal construction starts from an actual automorphic action and a
supplied quotient homomorphism. It uses the existing all-test full centre and
the published `AutomorphicAction.onQuotient` construction; it proves no
existence theorem for quotient group schemes.

`AutomorphicAction.isStable_center` works over every base scheme and for any
acting group scheme. A central point remains central under an automorphism
on every refinement of its test scheme. To check commutation with an arbitrary
point, apply centrality to its inverse-action image and then apply the original
action. Naturality identifies the restricted acted-on central point. This
argument requires no field, smoothness, connectedness or reducedness hypothesis.

`AutomorphicAction.onCenterQuotient` constructs the action on a supplied
quasi-compact, flat, surjective homomorphism whose full kernel range is the
full centre. Centre stability supplies the hypothesis of the existing
quotient-action construction. `onCenterQuotient_isEquivariant` and
`onCenterQuotient_unique` record its all-test equivariance and uniqueness.
The kernel may be nonsmooth, and points need only lift after base change.

For an actual `IsAdjointQuotient q` over any field,
`IsAdjointQuotient.action` constructs the action without additional morphism
property assumptions. The supplied quotient interface gives flatness and
scheme surjectivity. Connected reductivity of its source and adjointness of
its target give affineness; a morphism between these affine schemes is
quasi-compact. `action_isEquivariant` and `action_unique` give the corresponding
compatibility and uniqueness. The acting group is arbitrary; neither a split
torus nor algebraic closedness is needed.

`action_isEquivariant_of_square` considers actual adjoint quotients
`q : G → Q`, `p : H → R`, an equivariant `i : H → G`, and a supplied
`j : R → Q` with `i ≫ q = p ≫ j`. It proves equivariance of `j` for the
two canonical quotient actions. The proof pulls an arbitrary point of `R`
back along the fpqc map `p`, uses naturality, the square and equivariance of
`i`, `p` and `q`, then cancels the epimorphic base change. It does not assume
surjectivity on points over the original test scheme.

The constructions and deductions have internal provenance: they combine the
full-centre definition, point automorphisms, published quotient-action descent,
and its local-lifting equality criterion. They supply action data and
compatibility for the central-quotient step of semigroup comparison. They do
not prove centre containment in a semigroup group, a semigroup image or
intersection identity, inner factorization of the original action, or
existence, monicity, normality or closedness of the supplied map `j`.
