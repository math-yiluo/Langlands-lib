# Normal subgroups with proper homogeneous quotient

This internal construction compares two supplied quotients of the same
group. All schemes and fields may lie in an arbitrary universe `u`.

Let `i : N ⟶ G` be a homomorphism whose underlying relative scheme map is
monic. Let `r : G ⟶ R` be a represented fppf group quotient with actual
kernel range `range i`. Let `q : G.X ⟶ Q` be a flat, surjective,
quasi-compact morphism of relative schemes. Assume that equality of the
`q` images of any two points on every scheme test implies that their
right difference lies in `range i`.

`normalQuotientComparisonMap` is an actual morphism `Q ⟶ R.X`. It
descends `r` along the effective scheme epimorphism underlying `q`.
The group quotient's kernel identifies its fibers with right differences
in `range i`; the supplied implication for `q` therefore makes `r`
constant on every fiber of `q`. The following compatibility theorem
states `q ≫ normalQuotientComparisonMap ... = r.hom.hom`.

## Properness and the kernel

Assume also that the base field is algebraically closed, `G` is connected
and reduced, `Q` is proper over the field, and `R.X.left` is affine.
Connectedness passes to `Q` along the surjective continuous map, and
reducedness descends along its faithfully flat projection. The identity
of `G` supplies a rational point of `Q`.

The comparison map is constant at its value on that point by the
previously constructed theorem on affine-valued maps from a pointed
proper connected reduced scheme. Its value there is the identity of
`R`, since `r` is a group homomorphism. Consequently `r` sends every
point on every scheme test to the identity. Its actual scheme kernel
is exactly `range i`, so `range i = ⊤` as subgroup functors on all tests.
These are the conclusions of
`comp_eq_one_of_proper_homogeneousQuotient` and
`range_eq_top_of_proper_homogeneousQuotient`.

The final theorem
`isIso_of_normal_of_proper_homogeneousQuotient` takes
`NormalSubgroupQuotientStatement` as an explicit premise. Given a
normal closed subgroup of a smooth connected affine group and a
supplied proper homogeneous quotient as above, that premise supplies
the affine represented quotient. Smoothness makes `G` reduced.
The preceding range equality and the existing uniqueness of group
schemes representing the same subgroup functor identify `i` with an
isomorphism `N ≅ G`.

## Provenance and scope

This is an internal consequence of actual quotient descent,
the represented-kernel fiber identity, reduced faithfully flat
descent, proper connected affine-valued constancy, and uniqueness of
represented subgroup functors. It introduces no external structural
theorem.

For a normal Borel subgroup the final conclusion would say that the
Borel inclusion is an isomorphism. The proof here retains the
normal-subgroup quotient proposition and the existence and properness
of the homogeneous quotient as explicit inputs. It constructs none of
those missing structural inputs and does not prove the Borel
normalizer theorem.
