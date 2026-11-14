# Finiteness of the joint adjoint and cocenter homomorphism

Let `k : Type u` be any field, `G` a connected reductive group over `k`, and
`d : D ⟶ G` an actual derived-subgroup inclusion. Let `q : G ⟶ A` satisfy
`IsAdjointQuotient q`, and let `p : G ⟶ Q` be an fppf quotient by the full range
functor of `d`. Assume that the structure morphism of `Q` is affine and locally
of finite type. The proved definition `isFinite_adjoint_cocenter` states that the
underlying scheme morphism of the paired homomorphism
`lift q p : G ⟶ A ⊗ Q` is finite. No assumption on rational-point surjectivity is
used, and the kernel need not be smooth.

The auxiliary theorem `comp_lift_eq_one_iff` holds over any scheme base. On every
test scheme, a point maps to the identity under a paired homomorphism precisely
when both component images are the identity. The proof composes with the two
product projections and uses the product universal property for the converse.

For the finiteness assertion, the published
`derivedCentralIntersectionFiniteness` supplies a finite closed subgroup
`c : C ⟶ D` whose full range is the inverse image of `center G` under `d`.
The proof shows on every test scheme that the range of `c ≫ d` equals the range
of the actual kernel inclusion of `lift q p`. In one direction a point in this
intersection is central, so `q` kills it, and lies in the derived subgroup, so
`p` kills it. Conversely, a point killed by `p` factors through `D`, and its
being killed by `q` makes that factor lie in the supplied intersection `C`.
These are statements about full subgroup functors, including nonreduced tests.

Both inclusions represent the same subgroup functor. Their representing
group schemes are therefore isomorphic over `Spec k`, which transports the
finiteness of `C` to the actual kernel. The target product is affine and locally
of finite type; the source is smooth, connected and affine by reductivity.
The proved helper `isFinite_hom_of_finite_kernel` then gives the conclusion.

This is an internal geometric composition of published adjoint-kernel,
derived-intersection and image-factorization results. It is intended as a
prerequisite for bounded-preimage arguments on rational points; it does not
assert those analytic conclusions or prove KP Proposition 2.2.16 by itself.
