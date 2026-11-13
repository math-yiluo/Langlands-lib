# Eventual smoothness and fibre geometry over the actual integer rings

Authors: Worker 208 (complete Lean proof and first Markdown draft); Worker
1557 (source and interface verification, Markdown revision and submission).

`Langlands.Global.adelicSpreadEventualSmoothFiberGeometry` proves exactly
`Langlands.Global.AdelicSpreadEventualSmoothFiberGeometryStatement.{u}`.
It specializes the published filtered-ring descent theorems to the actual
arithmetic diagrams. The statement and its import closure are unchanged.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2) and Remark
3.5, and the first and third proof paragraphs of Theorem 4.5 on printed
p. 12. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The arithmetic specialization and the empty-initial-set and
perfect-constant-field extensions are derived, as explained in the
published statement's Markdown.

The implemented smoothness argument uses the noetherianity of the initial
integer rings to obtain finite presentation and quasi-separatedness from
the supplied finite-type models. It applies the published spectrum
smoothness descent theorem. The shared theorem
`Langlands.Global.property_baseChangeMap_iff` uses pullback symmetry to
identify that theorem's base-change convention with `Over.pullback`. It
applies to every isomorphism-invariant morphism property and is also reused
by `AdelicSpreadGeometricallyConnectedProof`.

For fibre geometry the argument forgets the algebra structure of each
actual arithmetic diagram, preserving its colimit, and applies the
published original-ring fibre-geometry descent theorem at the initial
integer ring. An outgoing arrow from that initial index is the literal
integer-ring inclusion into its target finite superlevel. The reverse
direction uses the corresponding arrow for a given finite superlevel.

For the conjunction, the implemented proof first obtains two stage
witnesses, then uses filteredness to choose a common stage receiving both
transitions. The model-morphism naturality squares are actual cartesian
squares. Smoothness pulls back across the first square. The full
nonempty, geometrically connected, pure-dimensional fibre locus pulls
back across the second square, using local finite type of the morphism.
The inverse image of the whole target remains the whole target, so the
common stage satisfies the full conjunction. Conversely each component
of a common-stage witness implies its generic-fibre component by its
separate descent equivalence.

The endpoint `adelicSpreadEventualSmoothFiberGeometry` proves exactly
`AdelicSpreadEventualSmoothFiberGeometryStatement` in the arbitrary
common universe. It retains empty initial sets, arbitrary perfect
function-field constants, and nonaffine and nonseparated supplied
finite-type models. It does not construct models of an arbitrary field
morphism or prove Lang–Weil, integral-point surjectivity or adelic
openness.
