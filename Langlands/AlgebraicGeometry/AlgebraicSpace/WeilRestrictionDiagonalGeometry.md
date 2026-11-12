# Geometry of represented algebraic-space equalizers

Author: Worker 117.

This is an internal prerequisite for the proof of
`WeilRestrictionDiagonalStatement`. Its main theorem,
`WeilRestrictionDiagonalGeometry.locallyOfFiniteType_diagonal`, says that the
full presheaf diagonal of every algebraic space over an arbitrary scheme is
representable with locally finite type scheme projections. No finite type
assumption on the algebraic space or its base is imposed. The universe parameter
is unrestricted.

The module also proves two categorical helpers. `diagonalSquare` expresses a
kernel pair as the pullback of a diagonal along the product of its two maps.
`property_prodMap` shows that a morphism property stable under base change and
composition passes to the product of two maps. The latter identifies a product
with the pullback over the terminal object and applies the pullback-map rule.

For the main theorem, choose an etale surjective scheme atlas `a : U → X`.
The product of this atlas with itself, using the product comparison isomorphism
for the scheme Yoneda functor, is again representable, etale and surjective.
After this cover, the diagonal is represented by the atlas kernel pair
`R → U × U`. Its composite with the second projection is etale. The cancellation
lemma for locally finite type scheme morphisms therefore shows that
`R → U × U` is locally of finite type. Uniqueness of pullbacks identifies this
map with the selected represented projection of the diagonal. Finally,
`relativeProperty_of_etale_atlas` descends the property. Mathlib's faithfully
flat descent for locally finite type morphisms and
`SchemeFlatPropertyDescent.descendsAlong_etale_surjective` supply the descent
instance.

Provenance: these are internal deductions from the Library's definition of an
algebraic space, its represented atlas API and the Mathlib categorical and
scheme morphism lemmas named above. No external literature assertion is added.
They supply the local finite type input for the equalizer route to the
Weil-restriction diagonal theorem; they do not prove that final theorem.
