# Elementary descent through the canonical smooth-relation quotient

This internal helper develops the algebra of the full pointwise quotient and
its etale sheafification from `SmoothRelationQuotientStatement`. It proves no
geometric quotient theorem and requires none of its outstanding geometric
conclusions. Its provenance is the direct universal property of the Lean
`Quotient` construction and of presheaf sheafification.

Fix an actual algebraic space `R` over a scheme `S`, endpoint maps to the
presheaf represented by an actual scheme `U` over `S`, and the full sectionwise
monomorphic equivalence-relation witness `h`. All test schemes and all their
morphisms remain in `Over S` at universe `u`.

`toQuotientPresheaf_eq_iff` identifies equality of pointwise quotient classes
with the original relation, including the existence of an actual section of
`R` with the two prescribed endpoints. `toQuotientPresheaf_surjective` proves
surjectivity on each section type of this pointwise quotient.
`toQuotientPresheaf_coequalizes` identifies the two endpoint composites.
`isPullback_toQuotientPresheaf` proves the full presheaf kernel-pair square.
The implemented proof works at every test scheme: endpoint injectivity gives
uniqueness, while equality of classes gives an actual arrow witness. The
pointwise pullback criterion then gives the presheaf pullback.

`quotientPresheafDesc` descends any natural transformation from the represented
presheaf that agrees on both endpoints. The construction uses `Quotient.lift`;
restricting representatives proves naturality. `toQuotientPresheaf_desc`
establishes the factorization, and `quotientPresheaf_hom_ext` gives uniqueness
by surjectivity on each section type.

`quotientMap_coequalizes` establishes the endpoint equality after etale
sheafification. `quotientSheafDesc` extends the pointwise descent map into any
etale sheaf using the actual sheafification universal property.
`quotientMap_desc` proves compatibility with the fixed canonical quotient map,
and `quotientSheaf_hom_ext` proves uniqueness. These maps cover all sheaf
sections, including those without global representatives.

The pointwise surjectivity and kernel-pair assertions concern
`quotientPresheaf`. This file does not assert that the etale sheafification
map has global representatives or prove its kernel-pair, fppf descent,
representable diagonal, smoothness, or existence of an etale scheme atlas.
Those geometric conclusions remain the separate quotient theorem obligation.
