# Structural package for the actual dynamic adjoint determinant

`Langlands.GroupScheme.dynamicAdjointDeterminantStructure` proves exactly the
published proposition `DynamicAdjointDeterminantStructureStatement.{u}` at an
arbitrary universe `u`. Its inputs are the original field, connected reductive
group scheme `G`, cocharacter, and arbitrary inclusions representing the dynamic
parabolic `P`, centralizer `M`, and unipotent subgroup `U` on every scheme test.
All affine, closed, smooth, finite-type and coordinate witnesses are conclusions.

The proof installs the affine and smooth structure-morphism properties supplied
by `IsConnectedReductive G`. It obtains affineness of the underlying scheme of
`G` by `isAffine_of_isAffineHom`. For each supplied representative, the published
`Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_*` results in
[`RepresentedStructure`](RepresentedStructure.md) transfer closedness from the
canonical affine representative. Their comparison isomorphisms commute with
the inclusions into `G` and use equality of the represented subgroup functors
on all scheme tests. The existing `IsClosedSubgroup.isAffineHom` then gives the
three affine structure morphisms.

`IsClosedSubgroup.locallyOfFiniteType` gives local finite type for each of
`P`, `M` and `U`: its structure morphism factors through the closed immersion
into the smooth, hence locally finite-type, ambient group. The proof applies
[`dynamicSmooth`](SmoothProof.md) separately to the three representation
witnesses to obtain smoothness of these structure morphisms.

With the affine and locally finite-type instances for `U`, the published
[`Lie.finiteDimensional_lieKernel`](../Lie/FiniteDimensional.md) instance supplies
finite dimension of `Additive (lieKernel U k)`, the actual dual-number identity
kernel. The final existential rank is
`Module.finrank k (Additive (lieKernel U k))`. The published
[`Lie.finiteCoordinates`](../Lie/ScalarExtensionCoordinates.md) supplies the
coordinate datum at precisely this rank, using actual Lie scalar extension
and a finite basis. Its naturality holds under every test-algebra map.

This is a derived assembly of those published results. It adds no
characteristic, splitness, reducedness or positive-rank premise; the trivial
cocharacter and rank zero are included. It constructs the structural and
linear-coordinate inputs specified by the target. It does not construct an
adjoint representation or a determinant character, which are separate
consumer constructions. The original statement and its imports are unchanged.
