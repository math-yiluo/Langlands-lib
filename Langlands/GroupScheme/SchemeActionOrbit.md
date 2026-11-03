# Underlying orbits and translations of scheme actions

Worker 1460.

This internal construction extends the published `SchemeAction H X` and
`SchemeActionRationalPoints` orbit-morphism API over an arbitrary base
scheme `S`. A section means a morphism from the terminal relative scheme,
which is `S` over itself.

The imported `orbitMap a x : H.X ⟶ X` is the action on the universal group
point and the constant section `x`. The new `orbit a x` is the range of
this actual morphism on the underlying topological spaces. No topology is
imposed on a set of rational points. The imported module already provides
the evaluation and all-test fixedness/constancy criteria; they are not
redefined here.

`translation a h` acts on `X` by the constant group section `h`.
Its evaluation formula follows from naturality of the action.
`translation_one` and `translation_mul` follow from the identity and
associativity laws of the action. `translationIso` uses the translation by
`h⁻¹` as the inverse.

`orbitMap_comp` proves that an equivariant relative scheme morphism
intertwines orbit morphisms. The equivariance premise is stated on every
test scheme. `image_orbit` then identifies the image of the underlying
orbit with the orbit of the image section.

The provenance is internal: these are direct constructions and proofs from
the published orbit-morphism API, action laws, cartesian products and
underlying maps of scheme morphisms. The file supplies no orbit-closedness,
fixed-point existence or affine-cover theorem. Those geometric results
remain prerequisites for the flag step of Chevalley's Borel-intersection
theorem.
