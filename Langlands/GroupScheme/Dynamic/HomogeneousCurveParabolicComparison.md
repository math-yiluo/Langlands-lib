# Actual dynamic parabolics from homogeneous quotient curves

Worker 1639. The contracting-subgroup vanishing construction adapts the
published `HomogeneousCurveUnipotentProof` implementation by Workers 1549,
1547, and 317; its new conclusion retains the all-test triviality proved
inside that implementation.

This internal comparison works over an algebraically closed field in universe
`u`, in every characteristic. Let `G` be pseudo-reductive, and let `b : B ⟶ G`
be a closed solvable subgroup. A split torus `T` maps to `B` through `t`, and
`ν` is any cocharacter of `T`. The supplied quasi-compact smooth surjective
map `q : G.X ⟶ Q` has exact all-test right-coset fibers for `B`. Its target is
separated over the field and has topological Krull dimension at most one.

`unipotent_eq_bot_of_noncontained_on_curve` assumes the ambient dynamic
identity-limit subgroup `U_G(ν)` is not contained in the all-test range of
`b`. It proves the literal subgroup-functor equality `U_B(ν) = ⊥`.
The quotient makes `B` smooth, and its closed immersion into the affine `G`
makes it affine. As in `curveUnipotentDataOfPseudoReductive`, the proof forms
the actual canonical affine representatives of `U_B(ν)` and `U_G(ν)` and
their induced closed inclusion. These groups are smooth, connected, and
unipotent by the published dynamic theorems. The quotient dimension formula
and signed tangent dimension formula give their dimension gap at most one.
`HomogeneousQuotient.unipotent_dimension_le_one` gives triviality of the
range of the internal representative in the ambient representative.
Monomorphisms reflect and preserve triviality under postcomposition; the
commuting square therefore identifies the actual range of the internal
inclusion into `B` with bottom. Its representation equality gives `U_B(ν) = ⊥`.

`Dynamic.unipotent_le_range_of_finrank_eq` is a general helper for a smooth
closed inclusion of affine field groups. It assumes equality of the intrinsic
dynamic tangent dimensions for one cocharacter in `B` and `G`.
The actual induced closed inclusion between their canonical smooth dynamic
representatives is an isomorphism by
`SubgroupFunctor.IsRepresentedBy.isIso_mapHom_of_finrank_eq`; its target is
connected by the dynamic connectedness theorem. The commuting square and
invariance of all-test range under an isomorphism then give
`U_G(ν) ≤ range b`. This uses an actual smooth closed inclusion, rather than
inferring containment between arbitrary subgroups from Lie containment.
`Dynamic.unipotent_or_neg_le_range_of_codimension_le_one` applies this to
the signed tangent dimension formula: an ambient Lie dimension gap at most
one forces one of the two signed dimensions to be equal, hence one entire
ambient contracting subgroup to be contained in `B`.

`parabolic_neg_isRepresentedBy_of_noncontained_on_curve` additionally assumes
that `B` is connected and contains the full actual centralizer `Z_G(ν)` on
every test scheme. Noncontainment of `U_G(ν)` excludes the positive choice in
the preceding signed alternative, so `U_G(-ν)` lies in `B`. The curve
vanishing result gives `U_B(ν) = ⊥`, and the published
`Dynamic.parabolic_neg_eq_top_of_unipotent_eq_bot` gives `P_B(-ν) = B`.
Functoriality of dynamic parabolics then puts `B` inside `P_G(-ν)`.
Centralizer invariance under cocharacter negation gives `Z_G(-ν) ≤ B`.
The all-test limit decomposition, expressed by
`Dynamic.parabolic_le_of_unipotent_le_of_centralizer_le`, gives the reverse
inclusion. Closedness supplies monicity, so this is exactly
`(P_G(-ν)).IsRepresentedBy b`.

`parabolic_or_neg_isRepresentedBy_of_curve` replaces the noncontainment
premise by properness, expressed as `¬ IsIso b`. Containment of both signed
contracting groups and of the centralizer would make the actual smooth
closed subgroup equal to `G`. The published signed noncontainment theorem
therefore supplies one sign that is not contained in `B`. Applying the
preceding result to that sign proves that `b` represents either `P_G(ν)` or
`P_G(-ν)`, with equality on every test scheme. The selected construction
`signedParabolicRepresentativeOfCurve` chooses such a cocharacter and returns
it together with its signed equality and actual representation witness.

This is derived internal content obtained from the named Library results;
it adds no classification theorem as an assumption. The actual quotient
curve, its properties and dimension bound, connectedness of `B`, properness,
and dynamic centralizer containment are explicit hypotheses. No maximal-torus,
Borel, root-rank, or regular-cocharacter assumption is used. Supplying these
geometric and centralizer hypotheses from the public rank-one Borel premises
remains separate work: this module does not prove
`RankOneBorelDynamicStatement`.
