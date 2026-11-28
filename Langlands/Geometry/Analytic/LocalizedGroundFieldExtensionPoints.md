# Compatible points under analytic ground field extension

For an isometric embedding `K → L` of complete ultrametric normed fields,
`pointProjection` is the natural projection from the underlying space of
the actual scalar extension. `pointComparison` maps the scalar-extended
source continuously to the topological space of compatible point pairs.
Its components are the projection to the original source and the actual
scalar extension of the morphism.

Given a localized analytic map `f : Y → X`, `exists_localizedPoint` lifts a
point of `Y` and a point of `X_L` with equal images in `X` to a point of `Y_L`.
For a compatible strong map, a chart through the chosen point of `Y` maps
into a target chart through its image. The extended target chart is the
inverse image of this target chart, so it contains the chosen point of `X_L`.
The compatibility of the two chart points follows from injectivity of the
target chart. `exists_spectrumPoint` gives a lift to the extended source
chart. Saturation preserves the underlying maps. For a localized fraction,
the inverse of the denominator on points moves the chosen source point to
the numerator's source. A lift for the numerator maps forward along the
extended denominator to the required lift. This proves surjectivity of
`pointComparison`.

`pointProjection_preimage_image` identifies the inverse image of the image
of any set under `f` with the image under `f_L` of the extended inverse image
of that set. It follows from compatible point lifting and naturality.
Taking unions gives the equivalence of joint surjectivity of a family and
of its scalar extension. Each original chart has a retained extended chart
in the saturated presentation, with range equal to the full inverse image
of the original range. Pulling a neighbourhood back under the continuous
projection therefore carries the finite chart-neighbourhood covering test
to the extended family.

This is the point comparison for the chartwise scalar extension and its
projection in Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), §1.4, pp. 29–30 (PDF pp. 26–27). The proof uses the affinoid comparison
on the same extended chart algebras and the actual localized morphisms. The
registered source `berkovich-1993-etale-cohomology` has SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
