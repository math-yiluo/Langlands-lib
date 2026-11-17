# Full linked roots from supplied structural statements

This internal reduction takes `SplitRankOneRootCellStatement` and
`SplitRootLieLineStatement` as explicit propositions to be proved independently.
It never invokes their existing excluded proof implementations. For every
root of a supplied split pinning over an arbitrary field, it constructs a
full `LinkedRootParametrization`, restricts these pairs to a
`SimpleRootCoordinateFamily`, and proves
`SplitSimpleRootCoordinatesExistStatement` from the two supplied statements.
It does not prove either structural input or the final Steinberg target.

First isolate a root in the centralizer of a cocharacter orthogonal to it
and generic on the other root directions. The actual centralizer inherits
connected reductivity, the split maximal torus and the orthogonal root datum.
Its roots are pairwise dependent. Apply the supplied rank-one root-cell
statement there. The open triple cell makes its two additive factors monic,
by inserting identity points in the other factors. Composing with the closed
centralizer inclusion gives monic additive maps in the original group,
with opposite full-torus characters and the literal all-test rank-one
relation. This is generic root isolation and functorial transport, not a
proof of rank-one positive-root uniqueness.

Reducedness of the supplied pinning excludes higher root multiples. The
supplied root-line statement gives the one-dimensional Lie space for each
of the positive and negative roots. The generic theorem
`VectorGroup.IsTorusEquivariant.represents_root_of_lie_line`, with those
explicit line witnesses, identifies both monic maps with their entire
intrinsic root functors. It retains arbitrary relative scheme tests,
including nonaffine and nonreduced tests. No call to the unconditional
`represents_root` theorem or to `splitRootLieLine` supplies these witnesses.

The actual chosen full-root pair and simple-root family are noncomputable
choices from these proved conditional constructions. The imported existing
canonical linked-root structure is used only for its fields, not its
existence proof or canonical choice. This unit reuses the clean generic
parts of root isolation, monicity, equivariance and subgroup uniqueness,
while replacing both contaminated existence inputs with explicit supplied
statements. It adds no external source assertion or final-target premise.
