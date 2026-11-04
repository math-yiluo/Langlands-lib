# Pure-dimensional residue-field fibres of actual scheme morphisms

This unit gives the concrete predicate needed for the last property in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p. 5, Theorem 3.4(2); the proof reference appears on p. 6.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

All declarations are in
`Langlands.AlgebraicGeometry.SchemeFiberGeometry`, in arbitrary universe `u`.
`HasPureDimension X d` means that **every irreducible component** of the
underlying topological space of the actual scheme `X`, with its subspace
topology, has topological Krull dimension exactly the natural number `d`.
Mathlib's `topologicalKrullDim` takes values in `WithBot ℕ∞`; the natural
number is cast into that type. Thus infinite-dimensional components do not
satisfy a finite dimension condition. This is the usual componentwise pure
dimension convention, rather than an assertion only about the largest
dimension of the whole scheme. The empty scheme satisfies this predicate
vacuously; nonemptiness is imposed separately in the fibre property.

`NonemptyGeometricallyConnectedPureDimensionFibers d f` requires, for every
point `y` of the target of an actual scheme morphism `f`, all three of:

- the actual fibre scheme `f.fiber y` is nonempty;
- its structure morphism `f.fiberToSpecResidueField y` to the spectrum of
  the residue field is geometrically connected, using Mathlib's predicate;
- that fibre scheme has pure dimension `d` in the componentwise sense above.

Mathlib constructs this fibre as a scheme pullback along the target point's
residue-field map. Geometric connectedness quantifies connectedness after
all field-valued base changes; it is not just connectedness over the
residue field. The definition imposes no properness, smoothness, flatness,
separatedness or affineness. Under finite presentation, the fibres are
finite-type schemes over fields, where this is the usual pure dimension
condition. The predicate itself also makes sense for arbitrary morphisms.

The short intrinsic lemmas are proved in this construction unit:

- `HasPureDimension.of_homeomorph` pulls an irreducible component back
  along a homeomorphism, uses the induced homeomorphism of that component,
  and applies invariance of topological Krull dimension.
- `hasPureDimension_iff_of_iso` applies the preceding result to the
  homeomorphisms underlying a scheme isomorphism and its inverse.
- `nonemptyGeometricallyConnectedPureDimensionFibers_iff` identifies the
  predicate exactly with geometric connectedness of `f` and pure
  dimension `d` of every residue-field fibre. It uses Mathlib's
  `GeometricallyConnected.iff_geometricallyConnected_fiber`. In the
  reverse direction Mathlib's connected-fibre instance supplies the
  explicit nonemptiness; hence no extra nonemptiness assumption is hidden.
- `NonemptyGeometricallyConnectedPureDimensionFibers.surjective` uses this
  comparison and Mathlib's surjectivity instance for geometrically
  connected morphisms.

These constructions translate the source property and supply internal
host comparisons. Descent along filtered colimits and invariance under
arbitrary field extension are separate mathematical obligations; this
unit does not assert either of them.
