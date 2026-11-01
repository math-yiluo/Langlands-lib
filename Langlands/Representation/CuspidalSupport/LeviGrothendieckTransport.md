# Actual whole-Levi transport on exact finite-length K0

Author: Worker 320.

This internal construction specializes continuous-group pullback on exact
finite-length smooth complex Grothendieck groups to the existing actual
permutation-matrix conjugation between product Levis. It introduces no new
literature theorem and changes none of the existing transport constructions.

Fix a field `F` with a topology making it a topological ring, block shapes
`B C : GeneralLinear.BlockShape n`, a permutation `w`, and an actual equality
`hw : CuspidalSupport.ConjugatesLevi B C w`. The published
`leviConjugationContinuous w hw` has direction `B.Levi F ≃ₜ* C.Levi F`.
The new `leviTransportK0` is pullback by its inverse, hence has direction
`K0(B.Levi F) ≃ₗ[ℤ] K0(C.Levi F)`. On an element of the target Levi, the
action is the original representation evaluated at inverse matrix conjugation.
This is the action of the existing `CuspidalSupport.transportFunctor`.

The groups are the exact Grothendieck groups of actual smooth complex
representations of finite group-algebra length, modulo relations from every
actual short exact sequence, including nonsplit ones. The field universe `uF`
and carrier parameter `uV` are independent; the displayed equivalence uses
carriers in `Type (max uF uV)`. The preservation lemmas also apply at an
arbitrary unsaturated carrier universe.

`transportFunctor_preservesFiniteLength` specializes the generic preservation
theorem for smooth pullback along a continuous multiplicative equivalence.
The functor agrees definitionally with inverse-conjugation pullback.
`transportFunctor_preservesShortExact` uses that every underlying linear map
is retained. Thus injectivity, surjectivity and equality of image and kernel
are retained. `leviTransportK0_toLinearMap` identifies the forward linear map
with the exact K0 map of the literal existing transport functor.
`leviTransportK0_finiteLengthClass` gives its class formula for that actual
output and any proof of its finite length.

`leviTransportK0_comp` states equality of the composite forward linear maps
with the map for the product permutation: transporting by `w`, then by `v`,
is transport by `v * w`. The proof tests all actual finite-length object
generators, uses the three generator formulas with explicit intermediate
length witnesses, and applies the identity linear equivalence to the
published equality `transport_transport`.

`leviTransportK0_eq_id_of_mem_blockWeyl` proves that a permutation preserving
each block induces the identity on the whole exact quotient. After the
generator formula, the published actual `transportWeylEquiv` identifies the
transported representation with the original one. That equivalence acts by
the corresponding genuine Levi permutation matrix.

All ranks, including the empty rank-zero shape, are allowed. No smoothness
outside the input category, irreducibility, admissibility, finite vector-space
dimension, or minimal-representative premise is added. These constructions
give no Jacquet or induction compatibility or Aubert identity.
