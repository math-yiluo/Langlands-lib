# Descent from compatible affine pushout models

This internal helper transfers target-local morphism properties from the maps in a compatible affine atlas to the global cocone legs, using the chart pullback squares and their canonical pullback isomorphisms. In particular, integral left maps and closed right maps yield the corresponding global properties.

If every model square is cartesian, the global square is cartesian. The proof pastes each model pullback with the right chart pullback, replaces the common inverse-image open by its canonical pullback model, and uses Mathlib's criterion for checking a pullback on an open cover of the left scheme.

The provenance is internal, derived from the preceding atlas construction and Mathlib's local property and pullback APIs. This helper assumes the atlas and all local properties; their construction remains a separate obligation for the exact statement.
