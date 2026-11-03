# Open-subscheme and fibre restrictions of sections

This internal interface compares two actual pullbacks of a module sheaf. If
`k : Y ⟶ A.toScheme` factors `g : Y ⟶ X` through an open subscheme, the
isomorphism `openFactorPullbackIso` composes the module pullback composition
isomorphism with transport along the factorization equality.

The lemma `openFactorPullbackIso_hom_openSection` says that this isomorphism sends
the pullback along `k` of `openSection M A t` to the direct pullback of `t` along
`g`, restricted to the whole of `Y`. Its proof uses the published comparisons of
`openSection` and `pullbackSection` with the adjunction section map, then the
composition and equality laws for that map. The fibre specialization identifies
this section with `fibreNeighbourhoodSection` on the actual scheme-theoretic
residue-field fibre.

For a line bundle, `openFactor_sectionOpen` and
`fibreNeighbourhoodSection_generationOpen` compare the entire generation opens
of these sections. The proof uses invariance of the generation open under a
module-sheaf isomorphism and the published generation-open pullback theorem.

The function `LineBundle.openPowSection` turns a section of `L`'s tensor power
over an open into a global power section of the actual restriction of `L` to
that open. It uses the existing pullback–tensor-power isomorphism.
`LineBundle.sectionOpen_openPowSection_fibre` identifies the inverse image of
this power section's whole generation open on the fibre with the whole
generation open of the actual fibre section, transported to the tensor power
of the fibre line bundle. Its proof applies invariance under the tensor-power
isomorphisms on both sides, then the preceding generation-open comparison to
the tensor-power line bundle. No compatibility between two different
tensor-power composition isomorphisms is needed.

The construction works for arbitrary module sheaves and arbitrary factorizations
through an open subscheme. It requires no properness, flatness or noetherianity.
It is derived from the existing Library pullback and section interfaces, and
does not prove section lifting or ampleness spreading.
