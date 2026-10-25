# Smooth morphisms have geometrically reduced fibres

`Langlands.AlgebraicGeometry.SmoothGeometricallyReduced.{u}` states that for
arbitrary Mathlib schemes `X` and `S` in universe `u`, every smooth morphism
`p : X ⟶ S` is geometrically reduced in Mathlib's sense. Thus for every field
`K` in that universe and every map `Spec K ⟶ S`, its base change has reduced
source. There is no properness, noetherian, nonempty, connectedness, or
characteristic restriction.

This is a derived relative formulation of Stacks Project Tag 056T, Lemma
33.25.4: a smooth scheme over a field is geometrically reduced. Smoothness is
stable under base change, so this field result applies to every field-valued
base change of `p`. Only the reducedness conclusion is stated here.

The retained source is `056T.html` in registered collection
`stacks-global-functions-field-and-fibre-criterion-2026-10-23`, directory SHA256
`c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`.
All geometric notions are existing Mathlib definitions; no new definition
artifact is needed. This file defines a proposition, and supplies no proof.
