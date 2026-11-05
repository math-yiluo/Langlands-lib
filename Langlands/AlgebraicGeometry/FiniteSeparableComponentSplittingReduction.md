# Reduction of finite separable component splitting to compact schemes

This is an internal reduction for the published
`FiniteSeparableComponentSplitting` proposition, in its original arbitrary
common universe. It does not prove the compact case or construct a splitting
field.

`baseChangeOpenIso` identifies the actual categorical scalar extension of an
open subscheme with the inverse-image open inside the scalar extension of
the ambient scheme. It composes Mathlib's pullback-pasting isomorphism,
pullback symmetry, and pullback/restriction isomorphism. The two coherence
lemmas identify the resulting inclusion and structure map.

`componentsGeometricallyIrreducible_of_open_baseChange` transfers geometric
irreducibility of all actual reduced components from the scalar extension of
an open containing all generic points to the scalar extension of the entire
field-scheme. The scalar-extension projection is flat, so the inverse-image
open still contains every generic point. The preceding isomorphism transports
the component property to that open. The generic-point open recovery theorem
then gives the component property for the entire scalar extension.

`finiteSeparableComponentSplitting_of_compactSpace` reduces the exact published
proposition to its compact-scheme case. Choose a compact open containing all
generic points. Its scheme structure is locally Noetherian because it is
locally of finite type over a field. Compactness makes it Noetherian, hence it
has finitely many irreducible components. Apply the assumed compact splitting
result to this open and use the preceding transport theorem. The conclusion
uses the same finite separable extension that the compact case supplies, and
the resulting component predicate unfolds to the actual vanishing-ideal
component condition in the original target.

The unit is derived from Mathlib's categorical pullback and Noetherian scheme
APIs and the generic-point open infrastructure. It adds no hypotheses to the
published unrestricted proposition. Its compact splitting hypothesis remains
a separate theorem to be supplied.
