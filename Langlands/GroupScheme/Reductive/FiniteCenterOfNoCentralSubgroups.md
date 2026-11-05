# Finite centres from the absence of smooth connected central subgroups

This is an internal derived helper for the central-torus semisimple-quotient
proof. Its provenance is the published reduced subgroup, identity component,
translation, and centre interfaces, together with Mathlib's finite type
zero-dimensional algebra criterion. It introduces no additional structural
assumption on reductive groups.

`HasTrivialSmoothConnectedCentralSubgroups G` is the Prop-valued predicate
that every smooth connected closed central subgroup of `G` has bottom range
on every test scheme. It is defined over every field and does not assume
existence of a centre. The finite-centre consequence below additionally
assumes that the field is algebraically closed.

Over an algebraically closed field, an affine group of finite type that has no
nontrivial smooth connected closed central subgroup has finite full
scheme-theoretic centre. The implemented argument takes the identity component
of the reduced centre, makes its inclusion trivial using the supplied
hypothesis, and obtains an open singleton in the centre. Translation makes
every closed point open. The Jacobson property then makes every point closed,
so the space is discrete. The coordinate algebra is a finite type
zero-dimensional algebra over a field and is therefore finite.

The main declaration is
`IsSchemeTheoreticCenter.isFinite_of_no_smooth_connected_central_subgroups`.
It takes an affine group `G` locally of finite type over an algebraically
closed field, a full centre representative `z : Z ⟶ G`, and the assumption
`HasTrivialSmoothConnectedCentralSubgroups G`. The reduced identity component supplied by
`ReducedSubgroup.exists_reducedIdentityComponent` maps into the centre and
is therefore killed by that assumption. Monicity of its inclusion makes
its identity morphism equal to its unit morphism. Since the spectrum of a
field is a singleton, its underlying space is a singleton as well. Its open
image is the required open singleton in `Z`.

`FiniteCenterOfNoCentralSubgroups.isFinite_of_open_singleton` translates
that singleton to all closed points. Their union is open. If the closed
complement contained a point, the Jacobson property would give it a closed
point, which is impossible; hence every point is closed and open.
`isFinite_of_discrete` transfers this discrete topology to the prime
spectrum of the global coordinate algebra. The spectrum has Krull dimension
at most zero, and the algebra is of finite type over the field, so
`Module.finite_iff_krullDimLE_zero` makes it a finite module. The affine
morphism criterion then makes the original structure morphism finite.

Only the topology passes through the reduced subgroup; the final coordinate
algebra and the finite structure morphism belong to the original centre
representative, retaining its nilpotents. No reductivity or smoothness of that
representative is assumed. This is an internal derivation and does not assert
the existence of the central torus or prove the host task by itself.
