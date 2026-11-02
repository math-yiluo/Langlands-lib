# Open spectral images from localized flat algebras

This internal auxiliary module supplies the openness input to
[SmoothRelationGoodPointOpenImage](SmoothRelationGoodPointOpenImage.md) from
a flat, finitely presented localization. All declarations are in
`Langlands.AlgebraicGeometry.SmoothRelationGoodPoint`.

Let `S → B → C` be a compatible tower of commutative algebras, and suppose
`C` is a localization of `B` away from `c ∈ B`, flat and finitely presented
over `S`. For every open subset `O ⊆ Spec B` contained in the basic open
`D(c)`, `isOpen_comap_image_of_flat_finitePresentation_away` proves that the
image of `O` in `Spec S` is open. The universes of the three rings are
independent.

Pull `O` back to `Spec C`. Flatness supplies going down, so Mathlib's
finite-presentation openness theorem makes the image of this preimage in
`Spec S` open. The image of `Spec C → Spec B` is exactly `D(c)`. The image
of the preimage of `O` is therefore `O ∩ D(c) = O`, and compatibility of
the algebra tower identifies the composite spectral map.

Specialize to `S = A[X_i]` and `C = B[c⁻¹]`, assumed etale over `S`.
For an open `O ⊆ D(c)` containing a given prime `q`, the theorem
`exists_prime_simpleIntegerRoots_of_etale_away` chooses a prime `r ∈ O`
with the same contraction to `A` as `q`. For every `i`, the image of `X_i`
at `r` satisfies an integer polynomial whose derivative is nonzero modulo
`r`. This is precisely the imported open-image theorem after the proved
openness lemma; etaleness supplies flatness and finite presentation.
There is no finite-index assumption, and the universes of `A`, `B` and
the index type are independent.

`simpleIntegerRootEtaleAway` packages the same actual choice as
`SimpleIntegerRootOpenImageData`, including membership, base contraction
and all simple-root equations.

Worker 303's coordinate route requires openness of images of open subsets
in a principal etale coordinate neighborhood. Worker 101 derived this
generic localization argument and its prime-choice consequences as a
separate prerequisite. No external source theorem is assumed beyond the
imported proved declarations. The module does not establish the coordinate
neighborhood, identify a point in a scheme orbit, or assert good-point
existence or the global etale slicing theorem.
