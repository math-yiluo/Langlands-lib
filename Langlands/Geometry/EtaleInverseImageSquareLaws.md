# Commuting squares of small étale inverse images

Let `f : Y ⟶ X`, `i : X' ⟶ X`, `j : Y' ⟶ Y`, and `g : Y' ⟶ X'`
be maps of schemes in universe `u`, with `h : j ≫ f = g ≫ i`. Write
`I_f` for `inverseImage f R` on sheaves of `ModuleCat.{u} R` on the small
étale sites, for a commutative ring `R : Type u`.
`inverseImageSquare R f i j g h` identifies `I_f ⋙ I_j` with
`I_i ⋙ I_g`. It uses `inverseImageComp` along both paths and
`inverseImageCongr` along `h`. Commutativity is the sole condition on
the square.

`inverseImageSquare_id` identifies the comparison for `i = 𝟙 X` and
`j = 𝟙 Y` with the inverse-image unit isomorphisms. For a second square
with `j' ≫ g = g' ≫ i'`, `inverseImageSquare_comp` identifies successive
comparisons with the comparison for `(j' ≫ j) ≫ f = g' ≫ i' ≫ i`.
The equation inserts the canonical composition maps on the two side
paths and is stated on each coefficient sheaf.

When `i` and `j` are étale, `inverseImageIsoRestriction` compares
their inverse images with `EtalePullback.restriction`. The laws
`inverseImageRestrictionSquare_id` and
`inverseImageRestrictionSquare_comp` use the existing
`inverseImageRestrictionSquare` and the restriction units and
composition maps. `inverseImageRestrictionSquare_congr` compares the
same square after equalities of the two étale arrows, using
`restrictionCongr` on both sides.

## Construction and proof

The internal proof that inverse-image equality transport is reflexive
uses the mate on the direct images. The underlying comparison on each
étale test is the identity by the two fiber product projections.
Transitivity then follows by substituting the equalities. For pasting,
the proof postcomposes both paths with the comparison to the inverse
image of the common composite. The published inverse-image
associativity law and transitivity of equality transport identify the
two resulting paths.

For the restriction laws, the comparison
`inverseImageIsoRestriction` identifies the original restriction
square with the one made of geometric inverse images. The comparison
is natural and respects identity and composition by
`EtaleInverseImageRestrictionCoherence`. Cancelling its isomorphism
components transfers the two square laws. Equality transport for the
restriction square reduces to transport along reflexive equalities.

These constructions are internal to the small étale functoriality of
`EtaleInverseImageExact` and `EtaleInverseImageRestrictionCoherence`.
