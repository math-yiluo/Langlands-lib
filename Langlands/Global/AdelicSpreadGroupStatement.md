# Actual adelic groups from specified arithmetic spreads

`Langlands.Global.AdelicSpreadGroupStatement` conjoins the function-field and
full number-field assertions about actual group-scheme points with their
previously defined topology from a specified finite-type arithmetic spread.

## Mathematical content

For every group scheme `G` over the original field, a finite set `S`, a finite-type
model `M` over the actual ring of integers outside `S`, and a specified
isomorphism from its generic fiber to `G.X`, the actual full-adele points form a
Hausdorff topological group. The topology is exactly
`curvePlaceSpreadAdelePointTopology` or `numberFieldSpreadAdelePointTopology`.
The carrier is the existing actual `RingPoint`, a morphism from the spectrum of
the actual full-adele algebra to the field scheme. The explicitly installed
group structure is Mathlib's existing group on `Hom` into the group object:
multiplication is the product lift followed by the group-scheme multiplication,
and inversion is postcomposition by its inverse morphism. Neither operation
nor its continuity is assumed as a field of an auxiliary structure.

The number-field clause also asserts local compactness and a countable base.
The function-field clause asserts these two additional properties under
`Finite k`; its Hausdorff topological group assertion retains arbitrary perfect
constant fields. The specified compatible rational-function actions and scalar
tower are retained, with no separability premise. Finite sets may be empty,
and number-field adeles include every infinite factor.

The model is finite type, expressed by `LocallyOfFiniteType M.hom` and
`QuasiCompact M.hom`. No affineness or separatedness assumption is imposed on
`G` or on `M`; no group structure on `M` or descended group law is required.
Existence of a finite-type model and its generic-fiber isomorphism is supplied
as explicit data, rather than asserted by this target.

## Source and derived scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.9, Section 4, states that finite-type group schemes over a global
field are automatically separated and have naturally locally compact Hausdorff
adelic topological groups; the preceding discussion includes a countable base.
The named topology here is the transported final topology of the actual
arithmetic stages described in that discussion.

The extension of continuity and Hausdorffness to arbitrary perfect function-field
constants is derived: finite-type arithmetic model products and the
independent-spread product comparison make the pointwise product lift
continuous, and field-scheme functoriality gives multiplication and inversion.
The published `Langlands.GroupScheme.fieldSeparated` theorem makes the group
scheme's diagonal a closed immersion. Closed-immersion preservation and the
same product comparison make the topological diagonal closed, proving
Hausdorffness with no separated-model assumption. Finite-constant and
number-field local compactness and countability follow from the existing
specified-spread topological properties. No local compactness or countability
claim is made for arbitrary infinite constant fields.

This pair supplies a proposition interface, not its proof or a model-existence
theorem. The all-five-sections obligations of parent task
`886bf565-95e9-4dc6-8a9d-73284a523668` remain separate.
