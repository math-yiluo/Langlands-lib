# Parabolic subgroup presentations and base change of ranges

Worker 1270. This is an internal categorical prerequisite for the exact
`Langlands.GroupScheme.ParabolicDynamicStatement` in `Absolute.BorelStatement`.
It does not prove that a dynamic subgroup is parabolic or that a parabolic
subgroup admits a cocharacter over its field of definition.

The definitions are the published `SubgroupFunctor.range`, its base change,
`IsClosedSubgroup`, and `IsParabolicSubgroup`. All equalities and inclusions of
subgroup functors apply to every test scheme, including non-affine schemes.
No characteristic, perfectness, splitness, or reductivity assumption is used.

`SubgroupFunctor.range_baseChange` proves that the range of a base-changed
homomorphism is the base change of its range. It transports a lift through the
pullback adjunction equivalence `baseChangePointsEquiv`; its compatibility with
postcomposition is `baseChangePointsEquiv_comp`.

`SubgroupFunctor.factorOfRangeLE` constructs a homomorphism between
two subgroup presentations whose underlying morphisms in the over category are
monomorphisms. The hypothesis is inclusion of their range subgroup functors.
The construction uses subgroup inclusions on points and the published
`IsRepresentedBy.lift`, whose naturality is immediate. Its compatibility with
the inclusions is `factorOfRangeLE_comp`, proved using `lift_comp_eq`.
`exists_factor_of_range_le` packages this construction as an existence statement.
The converse
`range_le_of_factor` restricts the factorization to each test scheme.

`IsParabolicSubgroup.iso_comp` preserves parabolicity when the source is changed
by an isomorphism. Closedness and smoothness are preserved by composition with
the isomorphism of underlying schemes. For the geometric Borel condition,
compose the given Borel factorization with the base change of the inverse
isomorphism.

`IsParabolicSubgroup.of_range_eq` uses the published
`IsRepresentedBy.isoOfIsRepresentedBy` to identify two closed subgroup
presentations with equal all-test ranges, then applies `iso_comp`.
`isParabolicSubgroup_iff_of_range_eq` applies this in both directions.

The source of the parabolic predicate is Milne, *Algebraic Groups* (2017),
Theorem 17.16, printed p.356 (PDF p.372), source
`milne-2017-algebraic-groups`. The predicate and its source convention are
explained in the published `Absolute.Borel` Markdown. These transport results
are derived from that predicate and the Library's categorical representation
interfaces; they are not independent structure theorems from Milne. The
implemented proof does not assume any of the unproved Borel, maximal-torus,
regular-cocharacter, or parabolic-dynamic statements.
