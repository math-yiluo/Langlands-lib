# Compatible affine neighborhoods for integral pinching

This derived internal development implements the compatible-neighborhood step
of Stacks Lemma 37.67.2 (Tag 0ECJ). It uses the actual integral-fibre principal
neighborhood construction in `IntegralFibreNeighborhoods`. The two section
lifts and the closed-image complement follow the same pattern as Worker
1770's shared finite-pinching neighborhood draft; no finiteness premise is
retained here.

`exists_affineOpen_lift_principal` lifts a section of the intersection of a
closed subscheme with an affine open. A closed immersion into an affine
scheme is affine and surjective on global sections. Choose a lift, take its
principal open, and take the image under the ambient open immersion.
Compatibility of restriction and principal opens identifies its inverse
image with the original principal open.

`exists_compatible_affineOpens_of_integral_at` starts with an affine open
`U₀` of `X` containing the image under `i` of the whole fibre of `j` over `y`,
and an affine open `V₀` of `Y` containing `y`. The integral-fibre
principal-neighborhood lemma gives a principal open on `i⁻¹(U₀)` containing
the fibre and lying in `j⁻¹(V₀)`. A section lift shrinks `U₀` to `U₁`, with
the fibre still contained in `i⁻¹(U₁)` and
`i⁻¹(U₁) ⊆ j⁻¹(V₀)`. Since integral morphisms are closed,
`W = Y \ j(Z \ i⁻¹(U₁))` is open, contains `y`, and satisfies
`j⁻¹(W) ⊆ i⁻¹(U₁)`.

Choose a principal open `D(s)` of `V₀` containing `y` and lying in `W`.
Pull `s` back to `i⁻¹(U₁)` and lift it to `U₁`. Its principal open `U`
has inverse image exactly `j⁻¹(D(s))`; this follows from the formula for
the principal open of a restricted pullback section and the containment
already established. The resulting compatible affine pair lies inside
the two original affine opens.

`exists_compatible_affineOpens_of_integral` chooses the initial opens from
the fibre-affine-neighborhood hypothesis and the affine basis on `Y`.
Its hypotheses are precisely a closed immersion `i`, an integral map `j`,
and that explicit neighborhood hypothesis. It produces compatible affine
opens around every point of `Y`. This unit does not construct the global
pushout or assert its categorical universal property.

`integralCompatibleAffineNeighborhood` packages this existence result as a
chosen pair of affine opens, together with membership of the given point in
the second open and equality of the two inverse-image opens. Its only
inputs beyond the schemes and maps are the same closed-immersion,
integrality and fibre-affine-neighborhood hypotheses.
