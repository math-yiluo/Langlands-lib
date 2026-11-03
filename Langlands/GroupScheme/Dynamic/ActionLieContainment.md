# Full-Lie criteria for action Dynamic functors

This internal auxiliary module concerns an arbitrary automorphic action of the
multiplicative group on a smooth connected affine group over a field. It proves
that the action parabolic is the whole group if every actual Lie point belongs
to that functor, and that the action centralizer is the whole group if every
actual Lie point belongs to the centralizer. The assertions retain arbitrary
fields and universe levels and equality on every test scheme.

The proof uses the actual semidirect group scheme `G ⋊ Gm`. Its underlying
scheme is the relative product. It is affine and smooth; it is connected because
`G` is connected and `Gm` is geometrically connected and universally open. The
latter properties follow from the published split-torus, smoothness and
geometric-connectedness theorems and Mathlib's connected pullback instance.

First, a smooth closed represented subgroup `F` of this semidirect product is
the whole group if it contains the entire acting factor and every Lie point of
the normal factor. For a Lie point `X` of the semidirect product, project to a
Lie point `t` of `Gm`, and multiply `X` by the inverse of the included `t`.
The result `Y` has trivial projection and therefore lifts to the normal factor.
The monomorphic inclusion reflects its identity reduction, so that lift is an
actual Lie point of `G`. The two containment hypotheses put `Y` and the included
`t` in `F`, hence put `X` in `F`. Representability then lifts `X` to the
representative; monomorphy again reflects the identity reduction. The published
`lieSubgroupEquality` theorem applies to this smooth closed representative in
the smooth connected ambient semidirect product and proves `F = top`. It does
not require connectedness of the subgroup representative.

Apply this criterion to the actual affine Dynamic parabolic or centralizer of
the acting-factor inclusion. Both representatives are smooth and closed by
published theorems. The entire acting factor centralizes itself because `Gm`
is commutative; it therefore belongs to both functors. The semidirect comap
identities convert the assumed original action Lie membership into membership
of the normal-factor Lie points. The criterion makes the ambient Dynamic
functor full, and the same comap identities make the original action functor
full.

The provenance is internal: this is a deduction from the published semidirect
maps and Dynamic comap identities, actual affine Dynamic representatives and
smoothness, geometric connectedness of smooth connected groups, and the smooth
full-Lie closed-subgroup equality theorem. It introduces no assumption about
semigroup realization, uniqueness or the host comparison target.
