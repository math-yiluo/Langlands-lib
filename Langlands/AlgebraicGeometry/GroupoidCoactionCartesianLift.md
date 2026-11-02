# Lifting coactions through source-cartesian coordinates

This internal construction is derived from the source-cartesian pushforward
and tensor scalar restriction lemmas. No cohomological vanishing or effective
descent hypothesis is assumed.

Let the commutative rings `B,C,D,P` have compatible source algebra structures,
with `e : P ≃ₐ[D] D ⊗[B] C` and compatible target maps `t,td`.
Let `M` be a `D`-module with a compatible `B`-module structure and an actual
base coaction `θ`. The additive map `cartesianLiftMap` is the inverse tensor
comparison applied to `θ.coaction`.

If this map is target semilinear over `D`, `cartesianLiftCoaction` constructs
an actual covering coaction. For each covering test algebra, give it the
composite `B`-algebra structure. Covering points then give compatible base
points. Apply the base counit and coassociativity laws and the canonical
map from tensors over `B` to tensors over `D`. The specialization comparison
proves the counit. The helper `restrictTensorScalars_lift_compose` proves
the corresponding composite comparison by induction on the inverse
cartesian tensor generators and proves coassociativity.

The map comparison is an identity after applying `pushforwardTensorEquiv`.
The final lemma therefore identifies the pushforward of the constructed
covering coaction with the original actual base coaction. The independent
semantic condition is precisely the stated target semilinearity assumption;
this construction does not assert it for an arbitrary `D`-module action.
