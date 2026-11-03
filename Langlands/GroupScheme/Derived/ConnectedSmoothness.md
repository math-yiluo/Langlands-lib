# Smoothness of derived subgroups of connected smooth affine groups

This internal module constructs a smooth representative of the full
commutator-image envelope and transfers smoothness to every actual derived
subgroup of a smooth connected affine group. The field and universe `u` are
arbitrary. Connectedness is ordinary `ConnectedSpace` of the ambient scheme;
no geometric connectedness, perfection or characteristic premise is added.

`smoothConnectedCommutatorImage k G hsm haff hconn` is an actual
`GeneratedImage (commutatorMap (𝟙 G) (𝟙 G))` together with its published
`HasSmoothConnectedGeneration` property. In particular, its group is smooth
and affine over the original field, geometrically connected, and receives a
dominant positive power of the commutator source.

The construction applies the published
`smoothConnectedAffineGeometry.2` to `G` twice. This supplies affineness,
local finite type and geometric integrality of the actual source
`G.X ⊗ G.X`. The product of the two identity sections is a rational point
of this source. Its composite with the actual commutator morphism is the
identity section, by `commutatorMap_one_left`. Thus the published theorem
`ImageGeneration.pointedImageGeneration` constructs the required envelope
representative and its full `HasSmoothConnectedGeneration` property.
Classical choice selects that witness; it adds no existence premise.

`IsDerivedSubgroup.smooth_of_connected` then proves `Smooth D.X.hom` for
any supplied `d : D ⟶ G` with `IsDerivedSubgroup d`, using exactly the three
ambient hypotheses above. The published
`IsDerivedSubgroup.smooth_of_generatedImage` compares `D` with the chosen
representative of the commutator envelope and transports smoothness along
the resulting isomorphism over the original field. The comparison uses the
full derived subgroup functor and closed envelope on all test schemes,
including nonreduced and nonaffine tests.

The provenance is an internal composition of the three imported Library
modules. No external structural theorem is introduced or assumed. Their
paired documentation records the geometric-integrality proof, pointed
image-generation proof, and all-test commutator-envelope comparison.

This supplies the smoothness obligation in the connected-reductive
semisimplicity task. The broader `DerivedSubgroupSmoothnessStatement`,
which allows disconnected ambient groups, remains a separate target.
Central-product existence and finiteness of the full central intersection
are not proved here.
