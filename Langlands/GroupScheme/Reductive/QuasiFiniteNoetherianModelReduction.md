# Noetherian models from finite coefficient homomorphism descent

This internal auxiliary converts a reductive finite coefficient model into the
exact `NoetherianQuasiFiniteModel` required by the published statement.
The coefficient subalgebra over a noetherian ring is finitely generated, so its
ring is noetherian by the finite type form of the Hilbert basis theorem.
Passing to its underlying subring of the original base ring preserves the
groups, their reductivity, the homomorphism and all three morphism properties.
The coefficient inclusion agrees with the subalgebra inclusion, so the stored
isomorphisms and recovery equation supply the required fields directly.

`reductiveQuasiFiniteNoetherianModel_of_descent` proves the unchanged target with
`HomGeneralStatement` and `DirectLimitReductiveStatement` as explicit premises.
It uses the integers lifted to the universe of the base ring as the initial
coefficient ring. The lifted ring is noetherian by its ring equivalence with the
integers, and the original base ring has the natural algebra structure over it.
Since the original supplied groups `G` and `H` are reductive, the finite
coefficient model is enlarged to make both model groups reductive, then the
conversion above applies. This construction works for every universe.

The provenance is internal composition of the finite coefficient group and
homomorphism models, simultaneous morphism property descent, direct-limit
reductivity, and Mathlib's finite type noetherian theorem. No finiteness of the
supplied homomorphism is assumed or deduced. The two descent premises are not
discharged in this auxiliary module.
