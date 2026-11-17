# Actual translated completions in the full determinant-band Hilbert space

This internal construction uses an actual cuspidal operator realization `S`,
positive matrix rank, a prescribed unitary central character and a supplied full
positive form `b` whose inner product is exactly the canonical determinant-band
integral. The number field has arbitrary universe and the usual compact
`AdeleQuotient` convention. The band-form identity is an explicit input; the
published `unitaryForm_inner` supplies it for the actual Petersson form.

For every actual adelic element `a`, `translatedToL2` maps each original vector to
the `Lp ℂ 2` vector represented by `q ↦ f(q a)` on the unchanged canonical band.
Published translated-band square integrability justifies this map. Its complex
linearity follows from the original quotient map's linearity and the `toLp`
identities. Its inner product is the actual integral of the translated pair.

The published arbitrary-translate pairing invariance under a unitary central
character shows that this translated map preserves `b`. A generic helper extends
any algebraic inner-product-preserving map into a complete inner-product space
to a linear isometry on the original form completion. It uses Mathlib's dense
isometric extension and proves agreement on the original carrier. Its image is
closed and equals the closure of the original algebraic image.

`translatedHilbertEmbedding` applies that helper to each actual translation. All
these embeddings have the same prescribed source completion and the same full
actual band `L²` target. They agree with `translatedToL2` on the canonical dense
embeddings, and their ranges are precisely the respective translated-image
closures.

The provenance is internal composition of translated-band integrability, the
published determinant-band invariant pairing and dense isometric extension.
There is no replacement form, norm, quotient or measure.

These are embeddings into the full band space. The module does not identify
their different ranges, prove that the original-image closure is translation
invariant, construct a group action on the source completion, or identify
differentiable smooth vectors. Smooth actual Hilbert coefficients and the
analytic annihilator argument remain separate obligations toward globalization
and unconditional cuspidal operator multiplicity one.
