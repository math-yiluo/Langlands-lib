# Residue coefficients, structure sections and products

Let `R` and `S` be commutative rings, let `S` be local, and let `φ : R →+* S`.
For an `R`-scheme `X`, write `i_X` for the actual residue-fibre projection and
`M_X = i_X* O_(X_K)` for `residueModule φ X`, where `K` is the residue field
of `S`. This internal construction uses the previously defined
`residueCoefficient φ f : M_X ⟶ f* M_Y` for a morphism `f : Y ⟶ X`.

`residueCoefficient_unit` proves that the residue coefficient morphism commutes
with the structure maps from the original schemes. Its section form,
`residueCoefficient_app_lift`, says that the image of `i_X.app U a` is
`i_Y.app (f⁻¹U) (f.app U a)`. The proof uses the composition law for structure
maps, equality transport along the residue projection square, and cancellation
of the pushforward composition isomorphism. The two elementary structure-map
laws are proved directly on sections.

For any index type `ι`, `residueProductCoefficient` constructs the morphism
`∏_ι M_X ⟶ f* (∏_ι M_Y)`. First it lifts the maps obtained by applying
`residueCoefficient` after each source projection; then it applies the inverse
of the product comparison isomorphism for pushforward. Pushforward preserves
these products. `residueProductCoefficient_π` proves that composition with the
pushforward of the `j`th target projection is exactly the `j`th source
projection followed by `residueCoefficient`. Its proof cancels the comparison
isomorphism and applies the universal property of the product.

No flatness, properness or Artinian hypothesis is used, and the index type need
not be finite. These are structure-section and product compatibility
constructions for the later elementary ideal coordinate square. This module
does not construct an ideal-product isomorphism or prove that square.
