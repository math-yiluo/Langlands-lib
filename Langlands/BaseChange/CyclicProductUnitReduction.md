# Unramified cyclic product units from the field unit lemma

`cyclicProductUnitReduction` proves `CyclicProductUnitReductionStatement`.
Assume the Library's `UnitFundamentalLemmaStatement` for field extensions.
Let `F` and `L` be the supplied p-adic fields and let `L/F` be unramified
cyclic of degree `d` with generator `τ`. Let `E/F` be a cyclic algebra of
degree `(m + 1) * d` with generator `σ`. The statement is for a supplied
topological algebra equivalence from `E` to the product of `m + 1` copies
of `L`. At each nonfinal index, `σ` takes the value from the following index.
At the final index, it takes the first value twisted by `τ`.

The ambient measure on `GL_{r+1}(E)` is the pushforward of the product of
copies of `sphericalHaar L r` by the inverse coordinate map. The product
test function is the indicator of the inverse image of the product of the
existing spherical subgroups in the factors. Over `F` the test is the unit
of `SphericalHeckeAlgebra F r` with Haar measure `sphericalHaar F r`. The
conclusion is `AreConcordant` for these functions and measures.

For vanishing off norms, the equivalence in
`cyclicProductGLCoordinates_isNorm_iff` transfers nonmembership in the norm
image to the field factor. The field unit premise gives the required
ordinary orbital integral vanishing.

For concordance at an associated pair, the proof sends an extension matrix
to the ordered product of its factor coordinates. The zeroth coordinate of
the full cyclic norm is the field cyclic norm of that product, and the
zeroth coordinate of the associated conjugator gives a field norm
association. The source twisted centralizer measure maps along
`cyclicProductCentralizerEquiv` to a right Haar measure on the field twisted
centralizer. Projecting the two measure pushforwards in `IsAssociatedMeasure`
to the zeroth coordinate proves association of this Haar measure with the
ordinary centralizer measure. The Library's quotient-measure existence
theorem supplies a compatible field quotient measure.

`cyclicProductUnitOrbitalIntegral_eq` then evaluates the product-side unit
orbital integral as the field-side twisted integral for this choice of
measure. The latter test function is the spherical Hecke unit because
the spherical subgroup has mass one. Applying the field unit lemma gives
the ordinary orbital integral with the supplied ordinary quotient measure.

This internal reduction follows Henniart–Lemaire I.2.4 and I.3.2, printed
pp. 15–16 and 25–26 (PDF pp. 23–24 and 33–34), in the regular semisimple
scope of the Library's `AreConcordant`. Applying it to local components
of a number-field extension requires their topological algebra coordinates
and the identification of their integral subgroups and normalized local
Haar measures.
