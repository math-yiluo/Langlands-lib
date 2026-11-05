# Identification of actual maximal-torus parameter schemes

Author: Worker 1630.

For arbitrary universe `u`, field `k : Type u`, group scheme `G` over
`Spec k` and morphism `j₀ : T₀.toGrp ⟶ G`, suppose that actual projections
`q : G.X ⟶ Q` and `q' : G.X ⟶ Q'` both satisfy the published
`IsMaximalTorusParameter j₀` predicate.
`IsMaximalTorusParameter.exists_iso` proves that there is an actual
isomorphism `e : Q ≅ Q'` in the category of schemes over `Spec k` with
`q ≫ e.hom = q'`. The definition `maximalTorusParameterIso` chooses one
such isomorphism, and `maximalTorusParameterIso_fac` gives this equality
for the chosen isomorphism.

The proof uses the supplied all-test fiber conditions. For every actual
test scheme `U` over `Spec k`, and all `g,h : U ⟶ G.X`, equality after `q`
and equality after `q'` are both equivalent to membership of `g⁻¹ * h`
in the same normalizer subgroup functor. Hence the two presentations
have exactly the same sectionwise kernel, on all tests. Smoothness and
surjectivity of the two projections make their represented presheaf maps
locally surjective for the actual slice fppf topology.

The imported theorem
`AlgebraicSpace.exists_iso_of_locallySurjective_of_same_kernel` then
constructs an isomorphism of represented presheaves compatible with both
projections. That theorem descends each map along the other effective
epimorphism in fppf sheaves and proves the two descended maps are inverse.
Full faithfulness of the lifted Yoneda functor recovers the actual
isomorphism over `Spec k`; faithfulness recovers its projection equality.
Thus the conclusion is an isomorphism of the input schemes, and is not
merely a correspondence between their field points.

This is an internal derived consequence of the published
`MaximalTorusParameter` and `FppfQuotientRepresentability` interfaces.
It uses only the projections' smoothness and surjectivity and the two
all-test fiber equivalences. The other conditions in the parameter
predicate are retained but not needed for this identification. There is
no additional hypothesis on the field, the group or the torus inclusion;
the predicate already supplies everything used in the proof.

This module does not construct a parameter scheme or a parametrization
of one. A substantive rationality or unirationality construction for a
representative is still needed before this isomorphism can transport
such a parametrization to another supplied parameter scheme.
