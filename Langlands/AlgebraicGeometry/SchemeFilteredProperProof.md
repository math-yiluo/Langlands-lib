# Proof of properness descent along actual limits

`properDescent` proves exactly
`Langlands.AlgebraicGeometry.SchemeLimitModel.ProperDescent` in arbitrary
universe `u`. The statement's paired Markdown records its source and scope.
Worker 105 authored the shared proof. Worker 706 reuses it here, adapting
the relative diagram helper calls to the current published
`SchemeLimitModel.Geometry.morphismDiagram` and
`morphismDiagram_cartesian` declarations.

The original source is Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2),
properness clause and its preceding finite-presentation convention.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The model-existence and relative assertions are derived supporting forms;
the other properties and whole-paper obligations remain separate.

The private `properSubalgebraDescent` first invokes the published separatedness
subalgebra descent theorem. The resulting finitely generated
`A₀`-subalgebra `T` of the final ring `A` is noetherian because `A₀` is
noetherian. The prescribed model pulled
back to `T` is separated. An actual iterated pullback identifies its further
base change to the final ring with the given proper morphism. The published
properness subalgebra theorem now gives a finitely generated `T`-subalgebra
`U`. Restrict scalars to the starting ring: finite generation follows from
composition of finite-type algebras. A second actual iterated pullback
transfers properness to the direct model over this restricted subalgebra.
The initial model was not assumed separated.

The private `propertyModelExistence` descends a finitely presented scheme
over the colimit first to a finitely generated subalgebra over lifted integers.
That algebra is noetherian. The preceding helper gives a further finitely
generated subalgebra on which the model is proper. This algebra is finitely
presented over lifted integers. The actual spectrum-limit factorization
lemma factors its base map through an original ring stage. Pullback to that
stage gives a finitely presented proper model, with an actual Cartesian
square recovering the original structure morphism.

The private `initialRingModelPropertyDescent` restricts to the actual
under-category tail of the initial ring. Its colimit is the original
colimit, by finality. It constructs a proper model there and compares it
to the prescribed model through an actual isomorphism over the colimit.
Proved original-ring isomorphism descent gives an isomorphism at a further
original stage. Properness transfers through this isomorphism and iterated
pullback. Base-change stability gives the converse.

The private `affineTargetDiagramPropertyDescent` passes from an affine
target diagram to its actual global-sections colimit. The canonical spectrum
isomorphisms transport its Cartesian squares, so prescribed-model descent
applies. `exists_property_level_of_affine_target` applies this to actual
base-change diagrams. `relativePropertyDescent` takes a finite affine cover
of the quasi-compact target, finds a stage for each chart, and uses
cofilteredness for a common stage. Base-change stability propagates the
chart properties, and target locality gives properness of the entire
morphism. The converse is base-change stability. Sources need not be affine.

The private spectrum and initial-ring helpers use the actual spectrum
limit and the actual under-category algebra tail, reindexing stages by
`op` and `unop`. The finite-presentation helper derives local finite
presentation of the relative morphism using the published
`Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp`, and its
quasi-compactness and quasi-separatedness by composition cancellation.
The six public intermediate theorems instantiate these helpers for
`IsProper`; the final theorem conjoins them. No additional source-model
separatedness, affineness, noetherian hypothesis, or transition-map
injectivity is used in the conclusions.
