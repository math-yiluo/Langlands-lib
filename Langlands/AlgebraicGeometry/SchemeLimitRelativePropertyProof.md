# Relative smooth and flat descent

The exact theorem is
`Langlands.AlgebraicGeometry.AffineLimit.relativeSmoothFlatDescent :
RelativeSmoothFlatDescent.{u}` for arbitrary universe `u`. Worker 105
authored the reused Lean proof and original explanation. Worker 1572
adapted the helper names to their published Library locations, checked
the proof against the published target and dependencies, and prepared
this focused submission.

This is a derived relative form supporting the smooth and flat clauses
of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Theorem 3.4(2), printed pp. 5–6. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source's prescribed original-ring relative specialization remains
a separate obligation, as do its other property clauses.

The proof targets `RelativeSmoothFlatDescent` in the unchanged
`SchemeLimitRelativePropertyStatement` pair. Private helpers
implement a common route for a property stable under base change and
local at the target, given its proved structural original-ring descent
theorem. The public conclusions instantiate this route with smoothness
and flatness and their respective proved descent theorems.

For a Cartesian natural transformation with affine target diagram, apply
global sections to the actual affine limit cone. Preservation gives an
actual filtered colimit of rings. The chosen stage source, with its
structural map followed by the affine target's canonical spectrum
isomorphism, is a finitely presented scheme over the chosen stage ring.
Transporting the Cartesian limit square along the spectrum isomorphisms
identifies the given limiting map with its actual pullback. Structural
descent gives an actual outgoing arrow in the ring diagram; transporting
the Cartesian transition square back gives the property for the original
scheme morphism at that stage. The source diagram need not be affine.

Apply this helper to the actual base-change diagrams over an affine
target. Then choose a finite affine cover of the general target, which
exists because its structural map to the affine base is quasi-compact.
Pull back the input morphism to each chart. Finite presentation persists
under base change. The chartwise argument yields finitely many stages;
cofilteredness supplies a common lower bound. The actual Cartesian
transition squares preserve the property at that stage, and locality
on the pulled-back target cover gives the original relative map's
property there.

Conversely, the actual Cartesian cone square transfers a stage property
to the limiting map by base-change stability. All isomorphisms used
in the proof come from actual pullback universal properties or affine
scheme duality. No assumed package of geometric descent properties
appears in either concrete theorem.

The public conclusions retain all hypotheses of the target, including
local finite presentation, quasi-compactness and quasi-separatedness of
`f` and quasi-compactness of `b`. Neither relative model is required to
be affine or separated. The argument introduces no noetherianity or
injectivity assumption on the original coordinate rings. The two
existential stages may differ. The natural transformation and its
Cartesian transitions are imported as `SchemeLimitModel.Geometry.morphismDiagram`
and `SchemeLimitModel.Geometry.morphismDiagram_cartesian`; structural
smoothness and flatness descent are imported by their Lean names.
