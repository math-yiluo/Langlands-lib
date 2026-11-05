# Geometric irreducibility of actual components and isomorphism transport

This internal comparison unit defines `ComponentsGeometricallyIrreducible f`
for an actual scheme morphism `f : X ⟶ S` in arbitrary common universe `u`.
It quantifies over exactly `irreducibleComponents X`. Each component is closed,
and its scheme structure is the actual vanishing-ideal closed subscheme.
The composite of that closed immersion with `f` must be geometrically
irreducible over `S`.

`fiberComponentsGeometricallyIrreducible_iff` identifies the published
`FiberComponentsGeometricallyIrreducible f y` definition exactly with this
component property on `f.fiberToSpecResidueField y`. This comparison is by
reflexivity: it changes neither the components nor the scheme structures.

The transport lemmas are derived from Mathlib's isomorphism invariance and
the published `GenericImagePattern` comparison of geometric irreducibility
for closed immersions having equal support. For a source isomorphism, the
proof pulls each component back to an actual maximal irreducible component,
then compares the composite closed immersion with the target component's
vanishing-ideal immersion by equality of their ranges. It does not assume
that scalar extension preserves reduced scheme structures. The reverse
implication uses the inverse isomorphism.

The base-isomorphism lemma applies Mathlib's cancellation of an isomorphism
for the geometric irreducibility morphism property, component by component.
The cartesian lemma combines this with the source isomorphism supplied by
base change of an isomorphism. The final fibre lemma applies it to Mathlib's
actual cartesian residue-field fibre comparison whenever the induced
residue-field map is an isomorphism.

These are internal transport results needed for Stacks 0551's generic-fibre
construction. They impose no finiteness, reducedness, separation, or
Noetherian hypothesis, and construct no splitting field or finite étale
cover. They do not assert invariance of the component property under arbitrary
field extension; that requires a separate argument.
