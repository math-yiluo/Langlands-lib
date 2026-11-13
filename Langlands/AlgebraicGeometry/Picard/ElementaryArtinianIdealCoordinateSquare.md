# Ideal coefficient squares from lifted-section formulas

Let `R` and `S` be commutative rings, with `S` local, let `φ : R →+* S`, and
let `X,Y` be schemes over `Spec R`. Write `I_X` for the actual closed-fibre
ideal `ideal φ X` and `M_X` for the pushed-forward residue structure module
`residueModule φ X`.

Given isomorphisms `eX : I_X ≅ ∏_ι M_X` and `eY : I_Y ≅ ∏_ι M_Y`,
`idealCoordinateCoefficient` transports the prescribed coordinatewise residue
map to `I_X ⟶ f* I_Y`, for any `f : Y ⟶ X`. The construction is
`eX.hom ≫ residueProductCoefficient φ ι f ≫ f*.map eY.inv`.
`idealCoordinateCoefficient_π` proves its coordinate square by cancelling
the target isomorphism and using the product coefficient projection law.
Neither construction requires a finite index type.

`compatible_unique` proves that compatibility with the actual ideal inclusions
determines an ideal coefficient morphism uniquely. The proof checks sections and
uses injectivity of the inclusion of a ring kernel. Consequently,
`coordinate_square_of_compatible` proves the prescribed coordinate square for
every compatible ideal morphism as soon as the transported morphism is
compatible.

`idealCoordinateCoefficient_compatible` gives a sufficient condition for that
compatibility. Here `ι` is equipped with a `Fintype`, and there is one list of
coefficients `v : ι → R` for both schemes. The inverse coordinates must satisfy

`(eZ.inv(s)).val = ∑ j, baseSectionHom Z.hom U (v j) * r j`

whenever the `j`th projection of `s` is the residue of the actual structure
section `r j`. This formula is assumed for `Z=X` on affine opens and for `Z=Y`
on all opens. The last hypothesis says that source residue sections lift on
affine opens. The proof checks the ideal-inclusion equality on the affine basis,
lifts every product coordinate, and uses `residueCoefficient_app_lift` to
identify the image coordinates. Applying both inverse formulas reduces the
equality to naturality of the base-section coefficients and preservation of
finite sums and products by the actual scheme section map.

`residueι_app_surjective` supplies affine lifting whenever `φ` is surjective.
Indeed, the composite of `φ` with the residue quotient is surjective, so its
spectrum map is a closed immersion. Its base change is the actual residue
projection, and a closed immersion is surjective on sections over affine opens.

This is internal sheaf infrastructure. The isomorphisms and common inverse
formulas are hypotheses; their construction in the elementary Artinian flat
case is separate work. This module assumes no cohomological injectivity,
properness, flatness, or Artinian condition and proves no unconditional ideal
decomposition.
