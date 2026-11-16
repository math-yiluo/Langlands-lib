# Geometry and field extension of generated root-subset groups

This supporting module derives existence, geometry and arbitrary-field base
change for `IsRootSubsetGroup` from the published family-generation results.
It does not prove an intersection theorem.

For a connected reductive group over a field, a maximal split torus and any
subset `X` of its actual relative roots, the generated group has a smooth,
affine, connected closed representative. Every supplied representative
satisfying `IsRootSubsetGroup` has the same geometry. No closure or convexity
assumption is needed for these conclusions.

`RootSubsetGroupGeometryStatement` uniformly packages the existence, the
geometry of every supplied representative, and compatibility with every
field extension in the same universe. `rootSubsetGroupGeometry` proves that
proposition.

The proof chooses a smooth closed representative of the whole-torus
centralizer and smooth connected closed representatives of each selected
relative-root functor. The centralizer is connected by
`IsSplitTorus.connectedSpace_centralizer`; closedness in the affine ambient
group supplies affineness. These choices form a family indexed by `Option X`,
with the centralizer at `none`. The all-test minimality condition
`IsRootSubsetGroup` is equivalent to `IsGeneratedByFamily` for this family.
`FiniteGeneration.exists_smooth_generated_family` gives existence. Uniqueness
of the range functor identifies every supplied representative with that
smooth connected representative, and geometry transfers through the resulting
isomorphism.

For any field extension in the same universe, including inseparable or
transcendental extensions, `IsGeneratedByFamily.baseChange` transports the
minimality condition. The identities `torusCentralizer_baseChange` and
`RelativeRoot.subgroup_baseChange` identify the extended generators with the
actual centralizer and actual character-orbit root functors. Thus the
base-changed inclusion satisfies `IsRootSubsetGroup` for the image of `X`
under the character-lattice base-change map. The extended torus is not assumed
to remain maximal split; this conclusion concerns the actual functors for
that extended torus.

The provenance is internal: the arguments combine the existing all-test
predicates, the published root realization, split-torus centralizer geometry,
and generated-family existence and base change. No new external-source
premise, Lie-image calculation or root-subset intersection assertion is used.
