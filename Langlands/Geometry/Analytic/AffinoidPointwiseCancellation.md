# Pointwise cancellation for bounded algebra maps

This internal helper treats bounded maps `f : R → S` and `g : S → T`
over a normed field. The field and three algebra carriers have independent
universes. It uses only their algebra structures and a spectrum point of `T`.
No completeness or valuation assumption is imposed.

For a finite-type composite, unramifiedness at the point descends to `g`.
The proof identifies the annihilator definition with unramifiedness of the
localized algebra, applies restriction of scalars, and returns to the
annihilator definition. Finite type of `g` follows from that of the composite.

Flatness of the composite descends when `f` is finite type and unramified
at the image point. The proof installs the actual scalar tower induced by
`f` and `g`, localizes at the three kernels, and applies Mathlib's
`Algebra.FormallyUnramified.flat_of_restrictScalars` to that tower.
Essential finite type is inherited from `f` after localization and restriction
of scalars. The final theorem combines these two conclusions to cancel
pointwise étaleness.

These are deductions from the Library's pointwise definitions and Mathlib's
restriction-of-scalars theorems. They do not construct finite analytic
neighborhoods or recognized affinoid preimages, so they do not prove the
strong all-pieces cancellation statement.

`PointwiseEtaleCancellationStatement K` records the resulting cancellation
law for every such triple of algebra carriers and actual bounded maps.
`pointwiseEtaleCancellation` proves this law by the combined helper above.
The submitted statement and its included helper proofs express only this
ring-level pointwise law, with no analytic neighborhood assertion.
