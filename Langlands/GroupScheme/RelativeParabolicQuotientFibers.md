# Field fibres of a supplied relative parabolic quotient

Author: Worker 1468.

This is an internal adapter between the published actual homogeneous quotient,
reductive base change and field parabolic properness interfaces. It assumes a
supplied `HomogeneousQuotient i`; it does not construct a relative quotient or
prove its properness over the original base.

For any base scheme `S`, group schemes `G` and `P` over `S`, and homomorphism
`i : P ⟶ G`, the module proves:

- `smooth`: if `G` is smooth, the structure morphism of a supplied quotient `Q`
  is smooth. Its projection is smooth and surjective by the quotient record,
  and its composite with the structure morphism is the structure morphism of
  `G`. The published smooth source descent theorem gives the result.
- `connectedSpace_fieldBaseChange`: if `G` is reductive, then at every actual
  field-valued point `f : Spec k → S`, the scheme of `Q.baseChange f` is
  connected. The actual pullback group is connected reductive by
  `IsReductive.isConnectedReductive_baseChange`. The quotient projection is a
  continuous surjection, so its target is connected.
- `geometricallyConnected`: the preceding assertion for all field-valued
  points is precisely geometric connectedness of `Q.scheme.hom`.
- `proper_fieldBaseChange`: if additionally the actual base-changed subgroup
  at `f` is parabolic, then the supplied `Q.baseChange f` is proper. This applies
  the published theorem `parabolicSubgroupQuotientProper` to that exact quotient,
  its separatedness, finite type, smooth surjective quasi-compact projection,
  and all-test coset criterion.

For an arbitrary commutative ring `R`, `parabolic_atFieldPoint` converts the
condition that `i` is parabolic after every field algebra base change into the
same assertion at every actual scheme morphism `Spec k → Spec R`. The proof
uses surjectivity of `Spec.map` on morphisms between affine schemes and equips
`k` with the algebra structure from the corresponding ring homomorphism.

`properConnectedFieldFiber` packages the actual `Q.baseChange f` with the
proved properness, smoothness and connectedness. Its value is definitionally
the published base-change construction, as recorded by
`properConnectedFieldFiber_val`. In particular its projection and exact coset
criterion are retained on all scheme tests over `k`, including non-affine and
nonreduced schemes.

All schemes, rings and fields have the same arbitrary universe parameter `u`.
The base ring need not be Noetherian, local or reduced. This module imposes no
new restriction on the zero ring or the subgroup `P = G`. It supplies fibre
geometry only: a passage from these fibres to properness over `R`, and the
unconditional existence of the quotient, remain separate obligations.

The provenance is internal: these are direct consequences and packaging of
the imported published Lean interfaces, rather than a translation of a new
assertion from the literature.
