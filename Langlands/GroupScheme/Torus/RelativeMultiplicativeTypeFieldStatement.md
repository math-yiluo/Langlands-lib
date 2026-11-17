# Statement: field-valued fibres of relative multiplicative-type groups

Worker 508.

`Langlands.GroupScheme.RelativeMultiplicativeTypeFieldStatement.{u}` is a
statement-only, `Prop`-valued definition. For every scheme `S`, every group scheme
`G` over `S` of relative multiplicative type, every field `k` in the same universe,
and every morphism `Spec k → S`, it asserts that the base change `G_k` has
multiplicative type in the Library's field-level sense. There are no additional
flatness, presentation, affineness, commutativity or connectedness hypotheses.
The statement makes no assertion about the converse or torsion ranks.

The relative predicate gives an fppf cover on which the group is diagonalizable
with finitely generated character group. The field predicate asks for a field
extension and an isomorphism to the affine diagonalizable model, also with
finitely generated character group; torsion in this group is permitted.
Specializing the statement to the Library's geometric point gives the forward
geometric-fibre implication used in the fibral criterion.

This is an internal comparison of the existing predicates in
[`RelativeMultiplicativeType`](RelativeMultiplicativeType.md) and
[`MultiplicativeType`](MultiplicativeType.md). Its expected proof uses their
published base-change constructions: take a point of a splitting-cover member
above the field-valued base, use its residue field as a splitting extension, and
compare the relative and affine diagonalizable models. This is the construction
already used for tori in
[`RelativeFieldComparison`](RelativeFieldComparison.md). No external result is
being restated. This file declares the comparison proposition and contains no
proof.
