# Conditional balanced cube assembly

The definition `Langlands.GroupScheme.fieldComparisonCubeIso` constructs an
actual isomorphism `cubePositive G L ≅ cubeNegative G L` on the
right-associated triple product of a group object over a field. Its inputs
are a proof of `FieldCubeIsomorphismStatement.{u}`, a field `K`, a group
object `G` over its spectrum, smoothness, properness and geometric
connectedness of the structure morphism, and an actual line bundle `L`
on `G`. No commutativity assumption is needed for this construction.

The theorem `Langlands.GroupScheme.fieldCubePullbackOfIsomorphism` then
proves that the published `FieldCubePullbackStatement.{u}` follows from
the same explicit cube-isomorphism premise. That premise remains unresolved.
This conditional supporting unit does not prove the unconditional balanced
cube statement or complete its task.

The construction works in arbitrary universe `u` and proceeds as follows.

1. Use the published theorem `pullbackTensorComparisonIsIso` as the
   preservation argument required by the balanced tensor helpers.
2. Pull the line bundle back to the field spectrum along the group identity
   section. The published `fieldLineBundleTriviality` theorem supplies an
   actual trivialization of this line bundle. Since the construction returns
   an isomorphism rather than a proposition, `Classical.choice` selects the
   witness from the theorem's `Nonempty` conclusion.
3. Package the positive four-factor tensor and the negative three-factor
   tensor on the right-associated triple product as actual line bundles.
   Their local rank-one properties follow from the preservation theorem
   through `positiveLineBundle` and `negativeLineBundle`.
4. Apply the three published identity-fibre face comparisons to the chosen
   trivialization. Specialize the supplied two-bundle cube theorem to three
   copies of the group object with the identity section as each base point.
   The given geometric hypotheses supply all nine hypotheses of that
   theorem. A second use of `Classical.choice` selects the actual
   isomorphism of the positive and negative tensors on the triple product.

The theorem takes the commutative group object and geometric hypotheses
quantified in `FieldCubePullbackStatement`, constructs the comparison with
`fieldComparisonCubeIso`, and applies `pullCubeIso` along the three
arbitrary maps from the arbitrary domain scheme. Its source and target are
definitionally the exact parenthesized tensors in that statement.

The only explicit premise of the theorem is the geometric comparison
statement. No condition on the domain scheme is added, and the tensor
preservation and identity-fibre triviality inputs are discharged by published
proofs. The unresolved premise must be replaced by a published unconditional
proof in the final exact-target theorem.

This is internal derived content by Worker 151, composing the published
balanced tensor, face and identity-fibre helpers with the two published
prerequisite proofs. Worker 316's contribution to identity-fibre transport
is credited in that imported helper's accepted provenance. The construction uses
those helpers by Lean name and introduces no new geometric argument.
