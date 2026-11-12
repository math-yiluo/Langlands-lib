# Eventual surjectivity of represented finite-presentation morphisms

This internally derived unit proves eventual surjectivity for a morphism of
finitely presented quasi-separated algebraic spaces that is independently
known to be representable at the original stage. It also gives the corresponding
reduction for any scheme morphism property stable under base change and
satisfying descent along surjective etale maps, provided that property's
scheme structural limit-descent theorem is available. The arbitrary cofiltered
category and universe of the host limit theorem are retained.

`SchemeTargetAtlas.toRepresented` equips an existing scheme target-atlas square
with a supplied representability witness. It preserves the actual source,
target, maps and cartesian square. It makes no assertion that a property of the
square implies representability of the original morphism.

`nonemptyFiberLocus_eq_univ_iff_surjective` identifies fullness of the actual
scheme nonempty-fibre locus with surjectivity of the scheme map. In
`surjective_schemeStructuralPropertyDescent`, the locus at each incoming stage
is constructible by the published finite-presentation fibre-locus theorem.
The target schemes are quasi-separated, including after the stage base changes.
The published model comparison identifies the limit locus with its inverse
image along the actual target limit cone. Constructible-set detection gives
fullness at an incoming stage. Conversely, surjectivity at a stage pulls back
to the limit by base-change stability.

`spaceLimitRelativePropertyDescent_of_representable` uses the published
`spaceLimitModelUniqueness` theorem and target-atlas construction to obtain a
finite-presentation scheme square at an incoming stage. The independent
representability hypothesis restricts to that stage and supplies the witness
for `toRepresented`. The published represented-chart limit theorem then reduces
the relative property to its scheme structural theorem. Canonical base-change
comparison transports the result back to the original diagram; the reverse
direction is preservation along the limit projection.

Finally, `isSurjective_limit_iff_of_representable` specializes this reduction to
scheme surjectivity. The existing fpqc surjectivity descent and
`SchemeFlatPropertyDescent.descendsAlong_etale_surjective` supply the required
etale-surjective descent instance. Here `IsSurjective` is the published relative
property on represented scheme pullback projections, not sectionwise
surjectivity of presheaves.

The provenance is entirely internal: actual nonempty-fibre constructibility
and limit comparisons from `SchemeLimitFiberLoci`, constructible detection from
`ConstructibleAffineLimit`, and the published model-uniqueness, target-atlas and
represented-chart results imported through `EventualTargetAtlasDescent` and
`SpaceLimitUniquenessProof`. No general effective descent of representability
is assumed or proved. This unit does not prove properness descent or the full
eight-property `SpaceLimitPropertyDescentStatement`; those remain obligations
of the host task.
