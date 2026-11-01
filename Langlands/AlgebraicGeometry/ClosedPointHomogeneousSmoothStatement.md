# Smoothness from transitivity on closed points

`Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothStatement.{u}` is
a proposition with the following quantifiers. For every algebraically closed
field `K : Type u`, every scheme `X : Scheme.{u}`, and every structure
morphism `f : X ⟶ Spec (CommRingCat.of K)` that is locally of finite type,
assume that `X` is reduced. Suppose that for every pair of closed points
`x, y : X` there is an actual scheme isomorphism `α : X ≅ X` satisfying
`α.hom ≫ f = f` and `α.hom x = y`. Then `f` is smooth.

Closedness here means that the singleton of the point is Zariski closed.
The automorphism must preserve the given structure morphism, so it is an
automorphism over `K`; a homeomorphism of the underlying space alone is
insufficient. The conclusion uses Mathlib's scheme-theoretic smoothness.
The proposition includes the empty scheme, does not assume a group law,
and requires neither quasi-compactness nor properness nor characteristic
zero.

This file defines the proposition and supplies no proof. It is an internal
derived geometric prerequisite for constructing the group scheme structure
on the reduced closure of actual two-power torsion. It is not a torsion-density
assertion and does not assert that this closure meets its hypotheses.

The formulation extracts the geometric argument in the pinned Mathlib
private lemma `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`, in
`Mathlib/AlgebraicGeometry/Group/Smooth.lean` at Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, authored by Andrew Yang
under Apache 2.0. The registered source ID is
`mathlib-group-smooth-5ed296525643`, SHA256
`4b78d0cacf95758052e21397c90cec6d556c443e38295ccd9ec4e6362c99bb6e`;
the complete source file was read, with the relevant private proof at
lines 28–61. No corresponding project errata note was found.
That proof uses the group structure to supply
automorphisms transitive on closed points; this statement keeps the
automorphisms as its explicit hypothesis. Reducedness over the perfect field
gives a dense smooth locus, the Jacobson property gives closed points in
each nonempty locally closed locus, and an automorphism transports
smoothness. This is the rationale for the broader formulation, rather than
a claim that Mathlib already exports this proposition.

The imports are exclusively Mathlib's closed-point correspondence and
scheme-smoothness modules.
