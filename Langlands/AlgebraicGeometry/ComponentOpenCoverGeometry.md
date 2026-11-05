# Open-cover assembly of geometric irreducibility of actual components

This internal derived module assembles the actual component predicate from an open cover of a scheme over a field. It extends the dense-open argument in `ComponentDenseOpenGeometry` to one component at a time. No finite-type, compactness, finiteness of components, reducedness, or separation hypothesis is used. Schemes and fields lie in an arbitrary common universe `u`; the cover's index type may lie in `v`.

`geometricallyIrreducible_component_of_open` takes an actual maximal irreducible component `C` of `X`, an open immersion `j : U → X` whose image meets `C`, and geometric irreducibility of all actual components of `U`. The inverse image of `C` is a maximal component of `U`. Pull back the vanishing-ideal closed immersion of `C` along `j`. Its support equals that of the vanishing-ideal closed immersion of this component of `U`. The published equal-closed-support comparison therefore gives geometric irreducibility of this pullback over the field. The pullback is an open subscheme of the reduced component of `X`, and its nonempty open image is dense in that irreducible component. The imported dense-open theorem gives geometric irreducibility of the actual reduced component of `X`.

`ComponentsGeometricallyIrreducible.of_openCover` chooses a member of the cover containing the generic point of each component and applies the preceding theorem. This proves the predicate on the entire scheme from its validity on every member of any open cover.

`openCoverBaseChangeIso` composes pullback pasting and symmetry to identify the scalar extension of a chart with the corresponding chart of the pulled-back cover. Its coherence lemma proves compatibility with the morphism to the new base. This is a categorical scheme isomorphism for arbitrary base change, without a field hypothesis.

`ComponentsGeometricallyIrreducible.of_openCover_baseChange` applies this assembly after a field-valued base change. Pulling the cover back to the scalar extension gives an open cover there. The preceding isomorphism identifies each member, over the new field, with the scalar extension of the original member. The source-isomorphism transport theorem transfers the supplied component properties, so the cover theorem applies.

This module supplies only transport and assembly. It does not construct a splitting field or prove the finite separable component-splitting existence statement.
