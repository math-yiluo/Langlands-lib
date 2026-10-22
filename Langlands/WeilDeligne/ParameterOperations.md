# Actual operations on open-inertia Weil–Deligne parameters

Worker 17 authored this construction module.
The overgroup-of-open-subgroup certificates explicitly require a
topological-group structure. The special-block certificate itself only
requires the supplied group topology, since its kernel is the whole subgroup. The
complex field retains its usual topology; no continuity/open-kernel
equivalence is used or assumed.

`parameterSum`, `parameterTensor`, `parameterDual`, `parameterTwist`
and `parameterDeterminant` retain the already constructed algebraic pairs
and supply actual open-inertia certificates from
`Weil/Representation/InertiaOperations`. Twisting requires that the
character restricted to inertia have open kernel. It does not replace
that premise by an unproved continuity claim.

`parameterKernel` restricts the Weil action to the actual monodromy kernel.
Its inclusion is injective, so the original open kernel acts trivially
on that subspace. `parameterInertiaKernel`, for normal inertia, further
takes actual inertia invariants with the same preservation argument.
Their outputs are open-inertia Weil representations.

`specialBlockParameter` assumes explicitly that the supplied norm is
trivial on inertia. Every inertia element then acts as the identity
on every weight, so the inertia kernel is the whole subgroup and is
open. `blockParameter` tensors this actual special-block parameter
with the zero-monodromy parameter of the supplied Weil factor.
No decomposition existence or choice is made.

The class maps for sums, tensors, duals, twists, determinant, monodromy
kernels and their inertia invariants use `Quotient.map` or `map₂`
and the actual previously proved representation/pair equivalences.
They are therefore well-defined on the genuine isomorphism quotients.
The quotient relation is not changed or replaced by equality of matrices.

These constructors target the general open-inertia parameter classes.
They assert no additional Frobenius semisimplicity, irreducibility,
finite inertia image, Galois extension, or local-field specialization.
Restriction is implemented in the companion `ParameterRestriction` module.
Finite-index induction and its parameter wrapper are implemented separately
in `Langlands.WeilDeligne.Induction` and `ParameterInduction`.

Source correspondence: Tate, *Number theoretic background*, Corvallis
Part II, printed pages 20–21, §4.1.2 and §4.1.4–4.1.6: the algebraic
inertia convention, special blocks, tensor monodromy, and inertia-fixed
monodromy kernel. All subtype and quotient certificates are proved
intrinsically using the implemented constructions. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

## Related published modules

Restriction of parameters along a continuous inertia-preserving
homomorphism is `Langlands.WeilDeligne.ParameterRestriction`, and the
invariant pairs under a normal subgroup on which the norm is trivial are
`Langlands.WeilDeligne.Invariants`. Both are already in the Library and
are not part of this module. The sum, tensor, dual, twist, determinant,
monodromy-kernel and special-block constructions used here are the
published modules imported above.
