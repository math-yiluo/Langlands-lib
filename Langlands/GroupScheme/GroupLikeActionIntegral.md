# Rigidity of actions with integral affine acting group

This internal construction defines `parameterAlgebra`: a field algebra
becomes an algebra over a parameter ring through a supplied field-algebra
map. Its `coefficientOriginalIso` identifies the composite field algebra
with the original field algebra by the identity on the underlying ring.
Naturality of an actual automorphic action transports the preceding
integral-parameter rigidity theorem across the associated affine
isomorphism. Consequently, one identity specialization of an acting
parameter point forces triviality on every affine test equipped with a
map from the parameter algebra.

The grouped results apply this to an acting Hopf algebra `D` over a field
`k`, with `D` an integral domain, and a target Hopf algebra `C` spanned by
its group-like elements. Take the parameter point to be the universal
`D`-valued point of `Spec D`. Its specialization by the counit is the
identity point. Every affine-test acting point is an algebra map from
`D`, so the preceding result shows that it acts trivially on every point
of `Spec C` over that same test algebra.

The actor and target are affine. Their actual product is therefore
affine and is isomorphic to an algebra spectrum. Evaluate the action
at the pullbacks of its two projections along this isomorphism. Affine
test triviality and cancellation of the isomorphism identify the actual
action morphism with the second projection
(`hom_eq_snd_of_integral_actor`). Composing with any pair of points
then proves `act_eq_self_of_integral_actor` on every scheme test,
including nonaffine and nonreduced tests.

The field, Hopf algebras, and tests share one arbitrary universe.
The target need not be reduced, smooth, or of finite type. The actor
is assumed to have integral coordinate algebra; a geometric
smooth-connected adapter and the centre-containment consequence are
separate steps. These are internal deductions from the published
coordinate and action interfaces and the preceding rigidity
construction. The host semigroup comparison remains open.
