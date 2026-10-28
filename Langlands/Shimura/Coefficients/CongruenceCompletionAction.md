# Continuous congruence-limit actions on completed coefficients

This internal construction composes the published discrete-completion topology,
coefficient congruence diagram, and profinite congruence-group limit. It gives
the actual completed coefficient module a jointly continuous action.

The construction starts with a compact open level `U` in a topological group,
a commutative ring `R`, an actual `R`-module action `M` of `U`, and openness of
every kernel of the actual action modulo `I^n`. The ring, group and module have
independent universes. All natural exponents, including zero, are retained.

`congruenceReductionLinear` is the existing action factored through its actual
kernel, now between the discrete quotient type synonyms. Its compatibility
with transitions is the published `congruenceCoefficientDiagram.comm`.
`congruenceCompletionTranslate` acts coordinatewise using a compatible family
of group elements and a compatible family of module elements. These two
compatibilities prove that its result belongs to the actual `AdicCompletion`
carrier. Linearity and continuity are proved coordinatewise.

`congruenceCompletionRepresentation` proves the identity and multiplication
laws, producing a monoid homomorphism into continuous linear endomorphisms.
Joint continuity follows from the coordinate continuity criterion: each
coordinate acts on a product of a discrete congruence group and a discrete
quotient module, and the group projection and module evaluation are continuous. The implementation
uses `congruenceGroupLimitProjection` to keep the quotient-group carrier explicit.
This does not require finiteness of the quotient module.

The same maps give a module-category action and a topological-space action.
`congruenceCompletionEvaluation` is the actual equivariant evaluation in the
module action category along the existing continuous group-limit projection.
`congruenceCompletionContinuousAction` bundles the proved joint continuity.
Restriction along the constructed original-level map equals the actual
completion map induced by the original linear action. The canonical algebraic
map from `M` into its completion is equivariant.

These coefficient actions follow the original left linear action; no inverse
is inserted. The inverse-right convention on the separate double-quotient
level spaces does not change the coefficient representation.

The final specialization uses the actual stable lattice constructed from an
algebraic coefficient representation and a compact open adelic level. Kernel
openness comes from the published derived algebraic continuity, without a new
orbit-continuity hypothesis. For nonzero rational scalar `m`, all actual
quotients are finite, so `algebraicCompactCoefficientCompletion_compact` proves
that the completed coefficient carrier is compact, with the explicit hypothesis
`hm : m ≠ 0`. The actual action is exported both as
`algebraicCompactCoefficientCompletionRepresentation` and as
`algebraicCompactCoefficientCompletionContinuousAction`.
The rational algebra, number field and representation space share universe
`u` in this existing specialization.

The provenance is internal composition of the published algebraic and
congruence constructions and pinned Mathlib compatible-family completion
operations. No new statement is attributed to Harris. This unit constructs
actions on the actual completion; it does not identify the initial lattice
with its completion, assert inverse-limit smoothness or scalar multiplication
continuity for a chosen ring topology, descend a sheaf, or compare cohomology.
