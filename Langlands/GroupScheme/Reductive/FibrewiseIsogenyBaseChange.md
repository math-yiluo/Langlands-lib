# Fibrewise isogenies at field-valued points and under base change

This is an internal transport unit for the fibrewise-isogeny proof. No
reductivity, smoothness, affineness, or noetherian hypothesis is used here.
The universe of the fields and schemes is the same arbitrary universe `u`.

`IsFieldwiseIsogeny f` means that the actual base change of the specified group
homomorphism `f` is a finite flat surjection at every field-valued point of its
base. The theorem `isFieldwiseIsogeny_iff_isFibrewiseIsogeny` identifies this
condition with the previously defined residue-field condition
`IsFibrewiseIsogeny f`.

To pass from residue fields to an arbitrary field-valued point, the proof factors
that point through the residue field of its image. It base changes the supplied
residue-fibre isogeny along the resulting field map. The canonical comparison
between iterated and direct pullbacks transports the isogeny condition back to
the original field-valued point. The reverse implication evaluates the fieldwise
condition at each canonical residue-field point.

The supporting theorem `isogeny_baseChange_comp_iff` proves that iterated and
direct base changes of a specified homomorphism are isogenies simultaneously.
Its proof uses naturality of the published pullback comparison and composition
with the two comparison isomorphisms, which are themselves isogenies.

`IsFieldwiseIsogeny.baseChange` follows by composing each field-valued point
with the base-change map and applying this comparison. The equivalence then
gives `IsFibrewiseIsogeny.baseChange` for every scheme morphism. A further helper
records that an isogeny satisfies the fieldwise condition by ordinary base-change
stability.

These are derived consequences of the published isogeny stability and pullback
comparison constructions and Mathlib's residue-field factorization. They do not
prove that fibrewise isogenies are isogenies, even for reductive groups or over
a discrete valuation ring.
